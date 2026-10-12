import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.kf_Hbog2
import Submission.Work.BoseBoxFock.kf_HchiGen
import Submission.Work.BoseBoxFock.kf_Hnn
import Submission.Work.BoseBoxFock.kf_Q3a
import Submission.Work.BoseBoxFock.kf_Q3b
import Submission.Work.BoseBoxFock.kf_contact_mu
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KafzDict` — the anti-normal dictionary of `H2ndHon`

This file collects the transport of the honest model `Work.BoseBoxFock.H2ndF` (FS
`eq:HLambdaSecond`) under the condensate splitting `Work.BoseB4.split` into the
anti-normal family `(pvec i, qvec i, KvecF i)` of `Fin 24`, i.e. it proves

  `split (H2ndF f g NH PHs E gHat0 x)
     = (∑ i : Fin 24, monoOp (pvec i) (qvec i) (KvecF f BNH PHs E gHat0 i)) (split x)`

whenever `NH` transports as `split (NH x) = lift BNH (split x)`.  The 24 slots are
the anti-normal monomials of FS `eq:subst-z`: the `(0,0)`/`(1,1)`/`(2,2)` slots of
the `a₀`-polynomial rows, the `(2,0)`/`(0,2)` Bogoliubov slots, the
`(2,1)`/`(1,0)`/`(1,2)`/`(0,1)` slots of the `χ̂`-rows, and the `(0,1)`/`(1,0)`
slots of the cubic `Q̃₃` row.

Route: the row lemmas (`kf_contact_mu`, `kf_HW`, `kf_Hbog1/2`, `kf_HchiGen`,
`kf_Hnn`, `kf_Q3a/b`) transport each row of `H2ndF`; the slot identity is a
`monoOp_add`/`monoOp_smul` reassembly.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

variable {m : ℕ} [NeZero m]

/-! ## 1. The scalar data of one parameter point -/

/-- FS's `ℓ⁻³`. -/
noncomputable def i3F {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode) : ℝ :=
  E.ell ^ (-(3 : ℝ))

/-- The contact coefficient `½ℓ⁻³(ĝ(0)+ĝω(0))` of `H2ndF`. -/
noncomputable def cHCF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) : ℝ :=
  (1 / 2) * i3F E * (gHat0 + E.W1omega0)

/-- The chemical coefficient `−μĝ(0)` of `H2ndF`. -/
noncomputable def cMuF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) : ℝ :=
  -(E.mu * gHat0)

/-! ## 2. The spectator words -/

/-- The spectator number `a_k†a_k` of the superposition `f k`. -/
noncomputable def nmF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (k : Mode) : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  (creOfE (f k)).comp (annOfE (f k))

/-- The `a₀`-free number sum `∑_k τ(k) a_k†a_k` of the kinetic row. -/
noncomputable def Bkin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.tau k : ℝ) : ℂ) • nmF f k

/-- The gap row's spectator: the excited number `n₊` of the model. -/
noncomputable def Bgap : cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ l : Excited m, (1 : ℂ) • ((creC (Excited m) l).comp (annC (Excited m) l))

/-- The `(W₁+W₁ω)`-weighted number sum of the `a₀†a_k†a_ka₀` row. -/
noncomputable def BW {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ s, ((w k : ℝ) : ℂ) • nmF f k

/-- The Bogoliubov pairing word `∑_k W₁(k) a_k a_{−k}`. -/
noncomputable def Bbog1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ s, ((w k : ℝ) : ℂ) • ((annOfE (f k)).comp (annOfE (f (-k))))

/-- Its adjoint `∑_k W₁(k) a_k† a_{−k}†`. -/
noncomputable def Bbog2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (w : Mode → ℝ) (f : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ s, ((w k : ℝ) : ℂ) • ((creOfE (f k)).comp (creOfE (f (-k))))

/-- The `χ̂`-weighted creation word `∑_k ĉ_k a_k†`. -/
noncomputable def BchiC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ) (φ : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ s, ((c * χ k : ℝ) : ℂ) • creOfE (φ k)

/-- The `χ̂`-weighted annihilation word `∑_k ĉ_k a_k`. -/
noncomputable def BchiA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ) (φ : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k ∈ s, ((c * χ k : ℝ) : ℂ) • annOfE (φ k)

/-- The cubic `Q̃₃` word `∑_{s,k} γ_{s,k} ã_s† a_{s−k} a_k`. -/
noncomputable def BQ3a {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (g f : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
    ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k))))

/-- Its adjoint `∑_{s,k} γ_{s,k} a_k† a_{s−k}† ã_s`. -/
noncomputable def BQ3b {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (g f : Mode → Fin m → ℝ) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ s ∈ S, ∑ k ∈ Ks, ((γ s k : ℝ) : ℂ) •
    ((creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s))))

/-- The `χ̂`-row creation word `(2,1)`. -/
noncomputable def Bc8 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Finset.univ : Finset Mode) E.hatChi (i3F E * E.W1 0) f

/-- The `χ̂`-row creation word `(1,0)`. -/
noncomputable def Bc8' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Finset.univ : Finset Mode) E.hatChi
    (2 * (i3F E * E.W1 0) + E.mu * E.W1 0) f

/-- The `χ̂`-row annihilation word `(1,2)`. -/
noncomputable def Ba8 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Finset.univ : Finset Mode) E.hatChi (i3F E * E.W1 0) f

/-- The `χ̂`-row annihilation word `(0,1)`. -/
noncomputable def Ba8' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Finset.univ : Finset Mode) E.hatChi
    (2 * (i3F E * E.W1 0) + E.mu * E.W1 0) f

/-- The `χ̂²`-row creation word `(2,1)`. -/
noncomputable def Bc9 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Work.BoseB7.excited Mode) E.hatChiSq (i3F E * E.W1omega0) g

/-- The `χ̂²`-row creation word `(1,0)`. -/
noncomputable def Bc9' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Work.BoseB7.excited Mode) E.hatChiSq (2 * (i3F E * E.W1omega0) + 0) g

/-- The `χ̂²`-row annihilation word `(1,2)`. -/
noncomputable def Ba9 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Work.BoseB7.excited Mode) E.hatChiSq (i3F E * E.W1omega0) g

/-- The `χ̂²`-row annihilation word `(0,1)`. -/
noncomputable def Ba9' {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Work.BoseB7.excited Mode) E.hatChiSq (2 * (i3F E * E.W1omega0) + 0) g

/-! ## 3. The 24 anti-normal slots of `H2ndF` -/

/-- The condensate-annihilation exponents of the 25 slots (indexed by `ℕ`, so that
the `Finset.range 25` expansion of the reassembly is computable).  Slot `i`
carries the anti-normal monomial `a₀^(pvecF i) (a₀†)^(qvecF i)`; slots past `24` carry
junk. -/
def pvecF : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 1
  | 9 => 0
  | 10 => 0
  | 11 => 2
  | 12 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 0
  | 16 => 2
  | 17 => 1
  | 18 => 1
  | 19 => 0
  | 20 => 1
  | 21 => 0
  | 22 => 0
  | 23 => 0
  | 24 => 1
  | _ => 0

/-- The condensate-creation exponents of the 25 slots. -/
def qvecF : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 2
  | 4 => 1
  | 5 => 0
  | 6 => 1
  | 7 => 0
  | 8 => 1
  | 9 => 0
  | 10 => 2
  | 11 => 0
  | 12 => 1
  | 13 => 0
  | 14 => 2
  | 15 => 1
  | 16 => 1
  | 17 => 0
  | 18 => 2
  | 19 => 1
  | 20 => 1
  | 21 => 0
  | 22 => 0
  | 23 => 1
  | 24 => 0
  | _ => 0

/-- **The 25 spectator words of the honest dictionary.**  `KvecF i` is the spectator
operator of the `i`-th anti-normal monomial of `H2ndF` under `split`, in the order
in which the rows of `H2ndF` produce them (rows 1-11, each row's slots left to
right); rows 4/5 contribute five slots and row 10 three. -/
noncomputable def KvecF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    ℕ → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)
  | 0 => Bkin f E
  | 1 => (((E.b / (2 * E.ell ^ 2) : ℝ)) : ℂ) • Bgap
  | 2 => (((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • BNH
  | 3 => (cHCF E gHat0 : ℂ) • 1
  | 4 => (- (cHCF E gHat0 : ℂ)) • ((4 : ℂ) • 1)
  | 5 => (cHCF E gHat0 : ℂ) • ((2 : ℂ) • 1)
  | 6 => (cMuF E gHat0 : ℂ) • 1
  | 7 => (- (cMuF E gHat0 : ℂ)) • 1
  | 8 => (i3F E : ℂ) • BW Finset.univ (fun k => E.W1 k + E.W1omega k) f
  | 9 => (((-(i3F E) : ℝ)) : ℂ) • BW Finset.univ (fun k => E.W1 k + E.W1omega k) f
  | 10 => (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ) • Bbog1 Finset.univ (fun k => E.W1 k) f
  | 11 => (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ) • Bbog2 Finset.univ (fun k => E.W1 k) f
  | 12 => Bc8 f E
  | 13 => - Bc8' f E
  | 14 => Ba8 f E
  | 15 => - Ba8' f E
  | 16 => Bc9 g E
  | 17 => - Bc9' g E
  | 18 => Ba9 g E
  | 19 => - Ba9' g E
  | 20 => ((i3F E * (E.W1 0 + E.W1omega0) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f
  | 21 => ((-(i3F E * (E.W1 0 + E.W1omega0)) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f
  | 22 => ((-(E.mu * E.W1 0) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f
  | 23 => BQ3a (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f
  | 24 => BQ3b (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f
  | _ => 0

/-! ## 4. The eleven rows of `H2ndF`, as named operators -/

/-- Row 1: the kinetic sum `Σ_k τ(k) a_k†a_k`. -/
noncomputable def rKin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ k : Mode, E.tau k • ((creOf m (f k)) ∘ₗ (annOf m (f k)))

/-- Row 2: the gap `(b/2ℓ²)(N − n₀)`. -/
noncomputable def rGap {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.b / (2 * E.ell ^ 2)) • (totNumOp m - n0)

/-- Row 3: the high-momentum gap `ε_T(b/2d²ℓ²) n₊^H`. -/
noncomputable def rGapH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (NH : RealFock m →ₗ[ℝ] RealFock m) (E : Work.BoseB7.Q3Env Mode) :
    RealFock m →ₗ[ℝ] RealFock m :=
  (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • NH

/-- Row 4: the contact term `½ℓ⁻³(ĝ(0)+ĝω(0)) (a₀†)²a₀²`. -/
noncomputable def rCon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ)) * (gHat0 + E.W1omega0)) •
    ((cre m 0) ∘ₗ (cre m 0) ∘ₗ (ann m 0) ∘ₗ (ann m 0))

/-- Row 5: `μĝ(0) n₀` (carrying a minus sign in `H2ndF`). -/
noncomputable def rMu {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.mu * gHat0) • n0

/-- The chemical-potential row with the sign flipped (used to replace `- rMu`). -/
noncomputable def rMuNeg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  - rMu E gHat0

/-- Rows 4 and 5 combined: the contact term minus the chemical potential. -/
noncomputable def rConMu {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  rCon E gHat0 - rMu E gHat0

/-- Row 6: `Σ_k (W₁(k)+W₁ω(k)) a₀†a_k†a_ka₀`. -/
noncomputable def rHW {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ))) •
    ∑ k : Mode, (E.W1 k + E.W1omega k) •
      ((cre m 0) ∘ₗ (creOf m (f k)) ∘ₗ (annOf m (f k)) ∘ₗ (ann m 0))

/-- The summand of the Bogoliubov pairing row at the mode `k`. -/
noncomputable def rPairH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (k : Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (cre m 0) ∘ₗ (cre m 0) ∘ₗ (annOf m (f k)) ∘ₗ (annOf m (f (-k)))
    + (creOf m (f k)) ∘ₗ (creOf m (f (-k))) ∘ₗ (ann m 0) ∘ₗ (ann m 0)

/-- Row 7: the Bogoliubov pairing. -/
noncomputable def rPair {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  ((1 / 2 : ℝ) * E.ell ^ (-(3 : ℝ))) • ∑ k : Mode, E.W1 k • rPairH f k

/-- `L₀ = ℓ⁻³Ŵ₁(0) n₀ − μŴ₁(0)`. -/
noncomputable def L0FKafz {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1 0) • n0 - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m)

/-- `L₁ = ℓ⁻³Ŵ₁ω(0) n₀`. -/
noncomputable def L1FKafz {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0

/-- The summand of the `χ̂` row at the mode `k`. -/
noncomputable def rChiH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (k : Mode) :
    RealFock m →ₗ[ℝ] RealFock m :=
  L0FKafz E gHat0 ∘ₗ (creOf m (f k)) ∘ₗ (ann m 0)
    + (cre m 0) ∘ₗ (annOf m (f k)) ∘ₗ L0FKafz E gHat0

/-- Row 8: the `χ̂` row. -/
noncomputable def rChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    RealFock m →ₗ[ℝ] RealFock m :=
  ∑ k : Mode, E.hatChi k • rChiH f E gHat0 k

/-- The summand of the `χ̂²` row at the mode `s`. -/
noncomputable def rChiOmH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (s : Mode) :
    RealFock m →ₗ[ℝ] RealFock m :=
  L1FKafz E ∘ₗ (creOf m (g s)) ∘ₗ (ann m 0) + (cre m 0) ∘ₗ (annOf m (g s)) ∘ₗ L1FKafz E

/-- Row 9: the `χ̂²` row. -/
noncomputable def rChiOm {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) : RealFock m →ₗ[ℝ] RealFock m :=
  ∑ s ∈ Work.BoseB7.excited Mode, E.hatChiSq s • rChiOmH g E s

/-- Row 10: `(L₀+L₁) Σ_k a_k†a_k`. -/
noncomputable def rHnn {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    RealFock m →ₗ[ℝ] RealFock m :=
  (L0FKafz E gHat0 + L1FKafz E) ∘ₗ (∑ k : Mode, (creOf m (f k)) ∘ₗ (annOf m (f k)))

/-- The summand of the cubic row at `(s, k)`. -/
noncomputable def rQ3H {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) (s k : Mode) :
    RealFock m →ₗ[ℝ] RealFock m :=
  (cre m 0) ∘ₗ (creOf m (g s)) ∘ₗ (annOf m (f (s - k))) ∘ₗ (annOf m (f k))
    + (creOf m (f k)) ∘ₗ (creOf m (f (s - k))) ∘ₗ (annOf m (g s)) ∘ₗ (ann m 0)

/-- Row 11: the cubic `Q̃₃` row. -/
noncomputable def rQ3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g f : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    RealFock m →ₗ[ℝ] RealFock m :=
  (E.ell ^ (-(3 : ℝ))) •
    ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs, (E.fL s * E.W1 k) • rQ3H g f E s k

/-- `H2ndF` with its eleven rows named. -/
noncomputable def H2ndRowsF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (NH : RealFock m →ₗ[ℝ] RealFock m) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) : RealFock m →ₗ[ℝ] RealFock m :=
  rKin f E + rGap E + rGapH NH E + rCon E gHat0 - rMu E gHat0 + rHW f E + rPair f E
    + rChi f E gHat0 + rChiOm g E + rHnn f E gHat0 + rQ3 g f PHs E

/-! ## 4c. The row 11 transport identity and `H2ndRowsF = H2ndF` -/

/-- `rQ3` with the `ℓ⁻³` distributed into the double sum (= `H2ndF`'s row 11). -/
lemma rQ3_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g f : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    rQ3 g f PHs E
      = (E.ell ^ (-(3 : ℝ))) • ∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
          (E.fL s * E.W1 k) • rQ3H g f E s k := by
  simp only [rQ3, Finset.smul_sum, ← smul_smul]

theorem H2ndRowsF_eq_H2ndF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (NH : RealFock m →ₗ[ℝ] RealFock m) (PHs : Finset Mode)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    H2ndRowsF f g NH PHs E gHat0 = H2ndF f g NH PHs E gHat0 := rfl

/-- The split of the sign-flipped chemical-potential row is the negative of the split
of the chemical-potential row. -/
lemma split_rMuNeg_neg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (y : RealFock m) :
    split (rMuNeg E gHat0 y) = - split (rMu E gHat0 y) := by
  rw [show rMuNeg E gHat0 y = - (rMu E gHat0 y) from rfl, map_neg]

/-! ## 4d. Normalisation lemmas for `monoOp` -/

/-- `monoOp` is `ℂ`-linear in the spectator slot, so a negation may be pulled inside. -/
lemma monoOp_neg (p q : ℕ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    monoOp p q (-B) = -monoOp p q B := by
  rw [show (-B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) = (-1 : ℂ) • B from
      (neg_one_smul ℂ B).symm, monoOp_smul]
  exact neg_one_smul ℂ (monoOp p q B)

/-- A real scalar in front of a `monoOp` is the corresponding complex scalar inside. -/
lemma real_smul_monoOp (p q : ℕ) (c : ℝ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    c • monoOp p q B = monoOp p q (((c : ℝ) : ℂ) • B) := by
  rw [show c • monoOp p q B
      = ((c : ℝ) : ℂ) • monoOp p q B from (Complex.coe_smul c (monoOp p q B)).symm,
    ← monoOp_smul]

/-- A negation of a complex scalar multiple. -/
lemma smulReal_neg (c : ℝ) (B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    -(((c : ℝ) : ℂ) • B) = (((-c : ℝ)) : ℂ) • B :=
  ((neg_smul ((c : ℝ) : ℂ) B).symm).trans
    (congrArg (fun z : ℂ => z • B) (Complex.ofReal_neg c).symm)

/-- A real scalar in front of a difference of two `monoOp`s. -/
lemma smul_monoOp_sub (c : ℝ) (p q p' q' : ℕ)
    (B B' : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    c • (monoOp p q B - monoOp p' q' B')
      = monoOp p q (((c : ℝ) : ℂ) • B) - monoOp p' q' (((c : ℝ) : ℂ) • B') := by
  rw [smul_sub, real_smul_monoOp, real_smul_monoOp]

/-! ## 4e. The slot vectors -/

@[simp] lemma pvecF_0 : pvecF 0 = 0 := by decide
@[simp] lemma pvecF_1 : pvecF 1 = 0 := by decide
@[simp] lemma pvecF_2 : pvecF 2 = 0 := by decide
@[simp] lemma pvecF_3 : pvecF 3 = 2 := by decide
@[simp] lemma pvecF_4 : pvecF 4 = 1 := by decide
@[simp] lemma pvecF_5 : pvecF 5 = 0 := by decide
@[simp] lemma pvecF_6 : pvecF 6 = 1 := by decide
@[simp] lemma pvecF_7 : pvecF 7 = 0 := by decide
@[simp] lemma pvecF_8 : pvecF 8 = 1 := by decide
@[simp] lemma pvecF_9 : pvecF 9 = 0 := by decide
@[simp] lemma pvecF_10 : pvecF 10 = 0 := by decide
@[simp] lemma pvecF_11 : pvecF 11 = 2 := by decide
@[simp] lemma pvecF_12 : pvecF 12 = 2 := by decide
@[simp] lemma pvecF_13 : pvecF 13 = 1 := by decide
@[simp] lemma pvecF_14 : pvecF 14 = 1 := by decide
@[simp] lemma pvecF_15 : pvecF 15 = 0 := by decide
@[simp] lemma pvecF_16 : pvecF 16 = 2 := by decide
@[simp] lemma pvecF_17 : pvecF 17 = 1 := by decide
@[simp] lemma pvecF_18 : pvecF 18 = 1 := by decide
@[simp] lemma pvecF_19 : pvecF 19 = 0 := by decide
@[simp] lemma pvecF_20 : pvecF 20 = 1 := by decide
@[simp] lemma pvecF_21 : pvecF 21 = 0 := by decide
@[simp] lemma pvecF_22 : pvecF 22 = 0 := by decide
@[simp] lemma pvecF_23 : pvecF 23 = 0 := by decide
@[simp] lemma pvecF_24 : pvecF 24 = 1 := by decide
@[simp] lemma qvecF_0 : qvecF 0 = 0 := by decide
@[simp] lemma qvecF_1 : qvecF 1 = 0 := by decide
@[simp] lemma qvecF_2 : qvecF 2 = 0 := by decide
@[simp] lemma qvecF_3 : qvecF 3 = 2 := by decide
@[simp] lemma qvecF_4 : qvecF 4 = 1 := by decide
@[simp] lemma qvecF_5 : qvecF 5 = 0 := by decide
@[simp] lemma qvecF_6 : qvecF 6 = 1 := by decide
@[simp] lemma qvecF_7 : qvecF 7 = 0 := by decide
@[simp] lemma qvecF_8 : qvecF 8 = 1 := by decide
@[simp] lemma qvecF_9 : qvecF 9 = 0 := by decide
@[simp] lemma qvecF_10 : qvecF 10 = 2 := by decide
@[simp] lemma qvecF_11 : qvecF 11 = 0 := by decide
@[simp] lemma qvecF_12 : qvecF 12 = 1 := by decide
@[simp] lemma qvecF_13 : qvecF 13 = 0 := by decide
@[simp] lemma qvecF_14 : qvecF 14 = 2 := by decide
@[simp] lemma qvecF_15 : qvecF 15 = 1 := by decide
@[simp] lemma qvecF_16 : qvecF 16 = 1 := by decide
@[simp] lemma qvecF_17 : qvecF 17 = 0 := by decide
@[simp] lemma qvecF_18 : qvecF 18 = 2 := by decide
@[simp] lemma qvecF_19 : qvecF 19 = 1 := by decide
@[simp] lemma qvecF_20 : qvecF 20 = 1 := by decide
@[simp] lemma qvecF_21 : qvecF 21 = 0 := by decide
@[simp] lemma qvecF_22 : qvecF 22 = 0 := by decide
@[simp] lemma qvecF_23 : qvecF 23 = 1 := by decide
@[simp] lemma qvecF_24 : qvecF 24 = 0 := by decide

lemma KvecF_0 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 0 = Bkin f E := by simp [KvecF]

lemma KvecF_1 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 1 = (((E.b / (2 * E.ell ^ 2) : ℝ)) : ℂ) • Bgap := by simp [KvecF]

lemma KvecF_2 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 2 = (((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • BNH := by simp [KvecF]

lemma KvecF_3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 3 = (cHCF E gHat0 : ℂ) • 1 := by simp [KvecF]

lemma KvecF_4 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 4 = (- (cHCF E gHat0 : ℂ)) • ((4 : ℂ) • 1) := by simp [KvecF]

lemma KvecF_5 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 5 = (cHCF E gHat0 : ℂ) • ((2 : ℂ) • 1) := by simp [KvecF]

lemma KvecF_6 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 6 = (cMuF E gHat0 : ℂ) • 1 := by simp [KvecF]

lemma KvecF_7 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 7 = ((cMuF E gHat0 : ℂ) * (-1 : ℂ)) • 1 := by simp [KvecF]

lemma KvecF_8 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 8 = (i3F E : ℂ) • BW Finset.univ (fun k => E.W1 k + E.W1omega k) f := by simp [KvecF]

lemma KvecF_9 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 9 = (((-(i3F E) : ℝ)) : ℂ) • BW Finset.univ (fun k => E.W1 k + E.W1omega k) f := by simp [KvecF]

lemma KvecF_10 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 10 = (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ) • Bbog1 Finset.univ (fun k => E.W1 k) f := by simp [KvecF]

lemma KvecF_11 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 11 = (((1 / 2 : ℝ) * i3F E : ℝ) : ℂ) • Bbog2 Finset.univ (fun k => E.W1 k) f := by simp [KvecF]

lemma KvecF_12 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 12 = Bc8 f E := by simp [KvecF]

lemma KvecF_13 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 13 = - Bc8' f E := by simp [KvecF]

lemma KvecF_14 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 14 = Ba8 f E := by simp [KvecF]

lemma KvecF_15 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 15 = - Ba8' f E := by simp [KvecF]

lemma KvecF_16 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 16 = Bc9 g E := by simp [KvecF]

lemma KvecF_17 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 17 = - Bc9' g E := by simp [KvecF]

lemma KvecF_18 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 18 = Ba9 g E := by simp [KvecF]

lemma KvecF_19 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 19 = - Ba9' g E := by simp [KvecF]

lemma KvecF_20 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 20 = ((i3F E * (E.W1 0 + E.W1omega0) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f := by simp [KvecF]

lemma KvecF_21 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 21 = ((-(i3F E * (E.W1 0 + E.W1omega0)) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f := by simp [KvecF]

lemma KvecF_22 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 22 = ((-(E.mu * E.W1 0) : ℝ) : ℂ) • BW Finset.univ (fun _ => 1) f := by simp [KvecF]

lemma KvecF_23 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 23 = BQ3a (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f := by simp [KvecF]

lemma KvecF_24 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    KvecF f g BNH PHs E gHat0 24 = BQ3b (Work.BoseB7.excited Mode) PHs (fun s k => i3F E * (E.fL s * E.W1 k)) g f := by simp [KvecF]

/-! ## 5. The eleven row transports, in slot form -/

/-- Row 1: the kinetic row `Σ_k τ_k a_k† a_k`. -/
theorem split_rKin {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rKin f E y)
      = (monoOp (pvecF 0) (qvecF 0) (KvecF f g BNH PHs E gHat0 0)) (split y) := by
  have h := split_weighted_number (m := m) (s := (Finset.univ : Finset Mode))
      (c := fun k => E.tau k) (φ := f) (fun k _ => hφ k) y
  have h2 : split (rKin f E y) = (monoOp 0 0 (Bkin f E)) (split y) := by
    simpa only [rKin, Bkin, nmF] using h
  rw [h2, KvecF_0]
  simp only [pvecF_0, qvecF_0]

/-- Row 2: the gap row `(b/2ℓ²)(N − n₀)`. -/
theorem split_rGap {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (y : RealFock m) :
    split (rGap E y)
      = (monoOp (pvecF 1) (qvecF 1) (KvecF f g BNH PHs E gHat0 1)) (split y) := by
  have h := split_gap (m := m) (c := E.b / (2 * E.ell ^ 2)) y
  rw [rGap, LinearMap.smul_apply, h, KvecF_1]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  rw [real_smul_monoOp]
  simp only [pvecF_1, qvecF_1, Bgap]

/-- Row 3: the high-momentum gap `ε_T(b/2d²ℓ²) n₊^H`. -/
theorem split_rGapH {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (NH : RealFock m →ₗ[ℝ] RealFock m)
    (hNH : ∀ y : RealFock m, split (NH y) = lift BNH (split y)) (y : RealFock m) :
    split (rGapH NH E y)
      = (monoOp (pvecF 2) (qvecF 2) (KvecF f g BNH PHs E gHat0 2)) (split y) := by
  rw [rGapH, LinearMap.smul_apply, map_smul, hNH, KvecF_2, ← LinearMap.smul_apply]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  rw [show (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • lift BNH
      = (((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) : ℝ)) : ℂ) • lift BNH from
        (Complex.coe_smul _ (lift BNH)).symm,
    ← lift_smul, ← monoOp_zero_zero]
  simp only [pvecF_2, qvecF_2]

/-- Row 4: the contact term `½ℓ⁻³(ĝ(0)+ĝω(0)) (a₀†)²a₀²`. -/
theorem split_rCon {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (y : RealFock m) :
    split (rCon E gHat0 y)
      = (monoOp (pvecF 3) (qvecF 3) (KvecF f g BNH PHs E gHat0 3)
          + (monoOp (pvecF 4) (qvecF 4) (KvecF f g BNH PHs E gHat0 4)
            + monoOp (pvecF 5) (qvecF 5) (KvecF f g BNH PHs E gHat0 5))) (split y) := by
  have hword : rCon E gHat0 y = (cHCF E gHat0) • (crePow (m := m) 2 (annPow (m := m) 2 y))
      + (0 : ℝ) • (crePow (m := m) 1 (annPow (m := m) 1 y)) := by
    rw [zero_smul, add_zero]
    simp only [rCon, cHCF, i3F, crePow_succ, crePow_zero, annPow_succ, annPow_zero,
      LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply]
  rw [hword, kf_contact_mu (m := m) (cHCF E gHat0) 0 y, KvecF_3, KvecF_4, KvecF_5]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  simp only [smul_sub, smul_add, smul_neg, ← smul_smul, sub_eq_add_neg, ← neg_smul,
    ← monoOp_smul, ← monoOp_neg, neg_mul, mul_neg, mul_one, Complex.ofReal_zero,
    zero_smul, monoOp_zero_fn, add_zero, zero_add,
    pvecF_3, qvecF_3, pvecF_4, qvecF_4, pvecF_5, qvecF_5, ← add_assoc]
  try rfl

/-- Row 5: the chemical-potential row with the sign flipped. -/
theorem split_rMuNeg {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (y : RealFock m) :
    split (- ((rMu E gHat0) y))
      = (monoOp (pvecF 6) (qvecF 6) (KvecF f g BNH PHs E gHat0 6)
          + monoOp (pvecF 7) (qvecF 7) (KvecF f g BNH PHs E gHat0 7)) (split y) := by
  have hword : - ((rMu E gHat0) y)
      = (0 : ℝ) • (crePow (m := m) 2 (annPow (m := m) 2 y))
        + (cMuF E gHat0) • (crePow (m := m) 1 (annPow (m := m) 1 y)) := by
    rw [zero_smul, zero_add]
    simp only [rMu, cMuF, n0, crePow_succ, crePow_zero,
      annPow_succ, annPow_zero, LinearMap.smul_apply, LinearMap.comp_apply,
      Module.End.one_apply, ← neg_smul]
  rw [hword, kf_contact_mu (m := m) 0 (cMuF E gHat0) y, KvecF_6, KvecF_7]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  simp only [Complex.ofReal_zero, zero_smul, monoOp_zero_fn, add_zero, zero_add, smul_add,
    smul_sub, smul_neg, sub_eq_add_neg, ← neg_smul, ← monoOp_smul, ← monoOp_neg, neg_mul,
    mul_neg, mul_one, pvecF_6, qvecF_6, pvecF_7, qvecF_7]
  try rfl

/-- Row 6: `ℓ⁻³ Σ_k (Ŵ₁(k)+Ŵ₁ω(k)) a₀†a_k†a_k a₀`. -/
theorem split_rHW {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rHW f E y)
      = (monoOp (pvecF 8) (qvecF 8) (KvecF f g BNH PHs E gHat0 8) + (monoOp (pvecF 9) (qvecF 9) (KvecF f g BNH PHs E gHat0 9))) (split y) := by
  have h := ss_conj1 (Finset.univ : Finset Mode) (fun k => E.W1 k + E.W1omega k) f
      (fun k _ => hφ k) y
  rw [rHW, LinearMap.smul_apply, map_smul, h, KvecF_8, KvecF_9, ← LinearMap.smul_apply]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  rw [smul_sub, real_smul_monoOp, real_smul_monoOp, sub_eq_add_neg, ← monoOp_neg, smulReal_neg]
  simp only [pvecF_8, qvecF_8, pvecF_9, qvecF_9, ← add_assoc]
  try rfl

/-- Row 7: the Bogoliubov pairing. -/
theorem split_rPair {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rPair f E y)
      = (monoOp (pvecF 10) (qvecF 10) (KvecF f g BNH PHs E gHat0 10) + (monoOp (pvecF 11) (qvecF 11) (KvecF f g BNH PHs E gHat0 11))) (split y) := by
  have hA := ss_conj2 (Finset.univ : Finset Mode) (fun k => E.W1 k) f (fun k => f (-k))
    (fun k _ => hφ k) (fun k _ => hφ (-k)) y
  have hB := kf_Hbog2 (Finset.univ : Finset Mode) (fun k => E.W1 k) f (fun k => f (-k))
    (fun k _ => hφ k) (fun k _ => hφ (-k)) y
  have hsum : (∑ k : Mode, E.W1 k • rPairH f k)
      = (∑ k : Mode, E.W1 k • ((cre m 0).comp ((cre m 0).comp
            ((annOf m (f k)).comp (annOf m (f (-k)))))))
        + (∑ k : Mode, E.W1 k • ((creOf m (f k)).comp ((creOf m (f (-k))).comp
            ((ann m 0).comp (ann m 0))))) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rPairH, smul_add]
  rw [rPair, LinearMap.smul_apply, map_smul,
    congrArg (fun F : RealFock m →ₗ[ℝ] RealFock m => F y) hsum,
    LinearMap.add_apply, map_add, hA]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [hB, KvecF_10, KvecF_11]
  rw [smul_add, ← LinearMap.smul_apply, ← LinearMap.smul_apply,
    real_smul_monoOp, real_smul_monoOp, ← LinearMap.add_apply]
  simp only [pvecF_10, qvecF_10, pvecF_11, qvecF_11, ← add_assoc]
  try rfl

/-- Row 8: the `χ̂` row `Σ_k χ̂_k (L₀a_k†a₀ + a₀†a_kL₀)`. -/
theorem split_rChi {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rChi f E gHat0 y)
      = (monoOp (pvecF 12) (qvecF 12) (KvecF f g BNH PHs E gHat0 12) + (monoOp (pvecF 13) (qvecF 13) (KvecF f g BNH PHs E gHat0 13) + (monoOp (pvecF 14) (qvecF 14) (KvecF f g BNH PHs E gHat0 14) + (monoOp (pvecF 15) (qvecF 15) (KvecF f g BNH PHs E gHat0 15))))) (split y) := by
  have h : split (rChi f E gHat0 y)
      = (monoOp 2 1 (∑ k ∈ (Finset.univ : Finset Mode),
              ((E.ell ^ (-(3 : ℝ)) * E.W1 0 * E.hatChi k : ℝ) : ℂ) • creOfE (f k))
          - monoOp 1 0 (∑ k ∈ (Finset.univ : Finset Mode),
              (((2 * (E.ell ^ (-(3 : ℝ)) * E.W1 0) + E.mu * E.W1 0) * E.hatChi k : ℝ) : ℂ)
                • creOfE (f k))
          + monoOp 1 2 (∑ k ∈ (Finset.univ : Finset Mode),
              ((E.ell ^ (-(3 : ℝ)) * E.W1 0 * E.hatChi k : ℝ) : ℂ) • annOfE (f k))
          - monoOp 0 1 (∑ k ∈ (Finset.univ : Finset Mode),
              (((2 * (E.ell ^ (-(3 : ℝ)) * E.W1 0) + E.mu * E.W1 0) * E.hatChi k : ℝ) : ℂ)
                • annOfE (f k))) (split y) := by
    simpa only [rChi, rChiH, L0FKafz, LinearMap.sum_apply, LinearMap.smul_apply] using
      kf_HchiGen (Finset.univ : Finset Mode) E.hatChi f (fun k _ => hφ k)
        (E.ell ^ (-(3 : ℝ)) * E.W1 0) (E.mu * E.W1 0) y
  rw [h, KvecF_12, KvecF_13, KvecF_14, KvecF_15, Bc8, Bc8', Ba8, Ba8', BchiC, BchiA, i3F]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  rw [sub_eq_add_neg, sub_eq_add_neg, ← monoOp_neg, ← monoOp_neg]
  simp only [pvecF_12, qvecF_12, pvecF_13, qvecF_13, pvecF_14, qvecF_14, pvecF_15, qvecF_15, ← add_assoc]
  try rfl

/-- Row 9: the `χ̂²` row `Σ_s χ̂²_s (L₁ã_s†a₀ + a₀†ã_sL₁)`. -/
theorem split_rChiOm {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hψ : ∀ s : Mode, s ≠ 0 → g s 0 = 0) (y : RealFock m) :
    split (rChiOm g E y)
      = (monoOp (pvecF 16) (qvecF 16) (KvecF f g BNH PHs E gHat0 16) + (monoOp (pvecF 17) (qvecF 17) (KvecF f g BNH PHs E gHat0 17) + (monoOp (pvecF 18) (qvecF 18) (KvecF f g BNH PHs E gHat0 18) + (monoOp (pvecF 19) (qvecF 19) (KvecF f g BNH PHs E gHat0 19))))) (split y) := by
  have hL1 : L1FKafz E = (E.ell ^ (-(3 : ℝ)) * E.W1omega0) • n0
      - (0 : ℝ) • (1 : RealFock m →ₗ[ℝ] RealFock m) := by
    rw [L1FKafz, zero_smul]
    abel
  have h : split (rChiOm g E y)
      = (monoOp 2 1 (∑ s ∈ Work.BoseB7.excited Mode,
              ((E.ell ^ (-(3 : ℝ)) * E.W1omega0 * E.hatChiSq s : ℝ) : ℂ) • creOfE (g s))
          - monoOp 1 0 (∑ s ∈ Work.BoseB7.excited Mode,
              (((2 * (E.ell ^ (-(3 : ℝ)) * E.W1omega0) + 0) * E.hatChiSq s : ℝ) : ℂ)
                • creOfE (g s))
          + monoOp 1 2 (∑ s ∈ Work.BoseB7.excited Mode,
              ((E.ell ^ (-(3 : ℝ)) * E.W1omega0 * E.hatChiSq s : ℝ) : ℂ) • annOfE (g s))
          - monoOp 0 1 (∑ s ∈ Work.BoseB7.excited Mode,
              (((2 * (E.ell ^ (-(3 : ℝ)) * E.W1omega0) + 0) * E.hatChiSq s : ℝ) : ℂ)
                • annOfE (g s))) (split y) := by
    simp only [rChiOm, rChiOmH, hL1, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [kf_HchiGen (Work.BoseB7.excited Mode) E.hatChiSq g
      (fun s hs => hψ s (Finset.mem_erase.mp hs).1)
      (E.ell ^ (-(3 : ℝ)) * E.W1omega0) 0 y]
  rw [h, KvecF_16, KvecF_17, KvecF_18, KvecF_19, Bc9, Bc9', Ba9, Ba9', BchiC, BchiA, i3F]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  rw [sub_eq_add_neg, sub_eq_add_neg, ← monoOp_neg, ← monoOp_neg]
  simp only [pvecF_16, qvecF_16, pvecF_17, qvecF_17, pvecF_18, qvecF_18, pvecF_19, qvecF_19, ← add_assoc]
  try rfl

/-- Row 10: `(L₀+L₁) Σ_k a_k†a_k`. -/
theorem split_rHnn {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rHnn f E gHat0 y)
      = (monoOp (pvecF 20) (qvecF 20) (KvecF f g BNH PHs E gHat0 20) + (monoOp (pvecF 21) (qvecF 21) (KvecF f g BNH PHs E gHat0 21) + (monoOp (pvecF 22) (qvecF 22) (KvecF f g BNH PHs E gHat0 22)))) (split y) := by
  have hL : L0FKafz E gHat0 + L1FKafz E
      = (E.ell ^ (-(3 : ℝ)) * (E.W1 0 + E.W1omega0)) • n0
        - (E.mu * E.W1 0) • (1 : RealFock m →ₗ[ℝ] RealFock m) := by
    rw [L0FKafz, L1FKafz,
      show (E.ell ^ (-(3 : ℝ)) * (E.W1 0 + E.W1omega0))
        = E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0 from by ring,
      add_smul]
    abel
  rw [rHnn, hL, kf_Hnn (Finset.univ : Finset Mode) f (fun k _ => hφ k)
      (E.ell ^ (-(3 : ℝ)) * (E.W1 0 + E.W1omega0)) (E.mu * E.W1 0) y,
    KvecF_20, KvecF_21, KvecF_22]
  refine congrArg (fun F : FockCore (cfock (Excited m)) →ₗ[ℂ] FockCore (cfock (Excited m)) => F (split y)) ?_
  simp only [BW, nmF, Complex.ofReal_one, one_smul, smul_sub, smul_add, smul_neg,
    ← smul_smul, ← monoOp_smul, sub_eq_add_neg, ← monoOp_neg, neg_mul, mul_neg, mul_one]
  rw [smulReal_neg, smulReal_neg]
  simp only [pvecF_20, qvecF_20, pvecF_21, qvecF_21, pvecF_22, qvecF_22, ← add_assoc]
  try rfl

/-- Row 11: the cubic `Q̃₃` row. -/
theorem split_rQ3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hψ : ∀ s : Mode, s ≠ 0 → g s 0 = 0) (hφ : ∀ k : Mode, f k 0 = 0) (y : RealFock m) :
    split (rQ3 g f PHs E y)
      = (monoOp (pvecF 23) (qvecF 23) (KvecF f g BNH PHs E gHat0 23) + (monoOp (pvecF 24) (qvecF 24) (KvecF f g BNH PHs E gHat0 24))) (split y) := by
  have hA := kf_Q3a (Work.BoseB7.excited Mode) PHs
    (fun s k => E.ell ^ (-(3 : ℝ)) * (E.fL s * E.W1 k)) g f
    (fun s hs => hψ s (Finset.mem_erase.mp hs).1) hφ y
  have hB := kf_Q3b (Work.BoseB7.excited Mode) PHs
    (fun s k => E.ell ^ (-(3 : ℝ)) * (E.fL s * E.W1 k)) g f
    (fun s hs => hψ s (Finset.mem_erase.mp hs).1) hφ y
  have hsplit : rQ3 g f PHs E y
      = (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
            (E.ell ^ (-(3 : ℝ)) * (E.fL s * E.W1 k)) •
              (((cre m 0).comp ((creOf m (g s)).comp
                ((annOf m (f (s - k))).comp (annOf m (f k))))) y))
        + (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
            (E.ell ^ (-(3 : ℝ)) * (E.fL s * E.W1 k)) •
              (((creOf m (f k)).comp ((creOf m (f (s - k))).comp
                ((annOf m (g s)).comp (ann m 0)))) y)) := by
    simp only [rQ3, rQ3H, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply,
      smul_add, Finset.sum_add_distrib, Finset.smul_sum, ← smul_smul]
  rw [hsplit, map_add, hA, hB, KvecF_23, KvecF_24, BQ3a, BQ3b, i3F, ← LinearMap.add_apply]
  simp only [pvecF_23, qvecF_23, pvecF_24, qvecF_24]

/-! ## 6. The 25-slot reassembly -/

/-- The `Finset.range 25` sum expanded into its 25 terms (right-nested). -/
lemma sum25_KvecF_eq {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) :
    (∑ i ∈ Finset.range 25, monoOp (pvecF i) (qvecF i) (KvecF f g BNH PHs E gHat0 i))
      = (monoOp (pvecF 0) (qvecF 0) (KvecF f g BNH PHs E gHat0 0)
          + (monoOp (pvecF 1) (qvecF 1) (KvecF f g BNH PHs E gHat0 1)
          + (monoOp (pvecF 2) (qvecF 2) (KvecF f g BNH PHs E gHat0 2)
          + (monoOp (pvecF 3) (qvecF 3) (KvecF f g BNH PHs E gHat0 3)
          + (monoOp (pvecF 4) (qvecF 4) (KvecF f g BNH PHs E gHat0 4)
          + (monoOp (pvecF 5) (qvecF 5) (KvecF f g BNH PHs E gHat0 5)
          + (monoOp (pvecF 6) (qvecF 6) (KvecF f g BNH PHs E gHat0 6)
          + (monoOp (pvecF 7) (qvecF 7) (KvecF f g BNH PHs E gHat0 7)
          + (monoOp (pvecF 8) (qvecF 8) (KvecF f g BNH PHs E gHat0 8)
          + (monoOp (pvecF 9) (qvecF 9) (KvecF f g BNH PHs E gHat0 9)
          + (monoOp (pvecF 10) (qvecF 10) (KvecF f g BNH PHs E gHat0 10)
          + (monoOp (pvecF 11) (qvecF 11) (KvecF f g BNH PHs E gHat0 11)
          + (monoOp (pvecF 12) (qvecF 12) (KvecF f g BNH PHs E gHat0 12)
          + (monoOp (pvecF 13) (qvecF 13) (KvecF f g BNH PHs E gHat0 13)
          + (monoOp (pvecF 14) (qvecF 14) (KvecF f g BNH PHs E gHat0 14)
          + (monoOp (pvecF 15) (qvecF 15) (KvecF f g BNH PHs E gHat0 15)
          + (monoOp (pvecF 16) (qvecF 16) (KvecF f g BNH PHs E gHat0 16)
          + (monoOp (pvecF 17) (qvecF 17) (KvecF f g BNH PHs E gHat0 17)
          + (monoOp (pvecF 18) (qvecF 18) (KvecF f g BNH PHs E gHat0 18)
          + (monoOp (pvecF 19) (qvecF 19) (KvecF f g BNH PHs E gHat0 19)
          + (monoOp (pvecF 20) (qvecF 20) (KvecF f g BNH PHs E gHat0 20)
          + (monoOp (pvecF 21) (qvecF 21) (KvecF f g BNH PHs E gHat0 21)
          + (monoOp (pvecF 22) (qvecF 22) (KvecF f g BNH PHs E gHat0 22)
          + (monoOp (pvecF 23) (qvecF 23) (KvecF f g BNH PHs E gHat0 23)
          + (monoOp (pvecF 24) (qvecF 24) (KvecF f g BNH PHs E gHat0 24)))))))))))))))))))))))))) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← add_assoc]

/-- **The dictionary of `H2ndF`**: the condensate splitting turns the honest model into
the 25-slot anti-normal family `(pvecF, qvecF, KvecF)`, provided the high-momentum
operator `NH` transports as `lift BNH`. -/
theorem hW_H2ndF {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (NH : RealFock m →ₗ[ℝ] RealFock m)
    (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hNH : ∀ y : RealFock m, split (NH y) = lift BNH (split y))
    (hφ : ∀ k : Mode, f k 0 = 0) (hψ : ∀ s : Mode, s ≠ 0 → g s 0 = 0) (y : RealFock m) :
    split (H2ndF f g NH PHs E gHat0 y)
      = (∑ i ∈ Finset.range 25, monoOp (pvecF i) (qvecF i) (KvecF f g BNH PHs E gHat0 i))
          (split y) := by
  rw [← H2ndRowsF_eq_H2ndF]
  simp only [H2ndRowsF, LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub,
    sub_eq_add_neg]
  rw [split_rKin f g BNH PHs E gHat0 hφ y,
    split_rGap f g BNH PHs E gHat0 y,
    split_rGapH f g BNH PHs E gHat0 NH hNH y,
    split_rCon f g BNH PHs E gHat0 y,
    split_rMuNeg f g BNH PHs E gHat0 y,
    split_rHW f g BNH PHs E gHat0 hφ y,
    split_rPair f g BNH PHs E gHat0 hφ y,
    split_rChi f g BNH PHs E gHat0 hφ y,
    split_rChiOm f g BNH PHs E gHat0 hψ y,
    split_rHnn f g BNH PHs E gHat0 hφ y,
    split_rQ3 f g BNH PHs E gHat0 hψ hφ y]
  simp only [← LinearMap.add_apply]
  congr 1
  rw [sum25_KvecF_eq]
  simp only [← add_assoc]

/-- **The exact `c`-number substitution** (FS `eq:IntroK(z)`): the expectation of the
honest model at a 25-slot dictionary vector is the Gaussian integral of its anti-Wick
symbol `Σ_i z^{pvecF i} z̄^{qvecF i} KvecF i`. -/
theorem bomb_H2ndF_eq_integral {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (NH : RealFock m →ₗ[ℝ] RealFock m)
    (BNH : cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ)
    (hNH : ∀ y : RealFock m, split (NH y) = lift BNH (split y))
    (hφ : ∀ k : Mode, f k 0 = 0) (hψ : ∀ s : Mode, s ≠ 0 → g s 0 = 0)
    (Ψ : RealFock m) :
    bomb m Ψ (H2ndF f g NH PHs E gHat0 Ψ)
      = ∫ z : ℂ, (∑ i ∈ Finset.range 25,
            z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i) *
              inner ℂ (Phi (split Ψ) z)
                ((fun i => KvecF f g BNH PHs E gHat0 i) i (Phi (split Ψ) z))).re
          ∂gauss := by
  have hW : ∀ x, split (H2ndF f g NH PHs E gHat0 x)
      = (∑ i ∈ Finset.range 25, monoOp (pvecF i) (qvecF i)
          ((fun i => KvecF f g BNH PHs E gHat0 i) i)) (split x) :=
    hW_H2ndF f g NH BNH PHs E gHat0 hNH hφ hψ
  have hint : MeasureTheory.Integrable (fun z : ℂ => ∑ i ∈ Finset.range 25,
      z ^ (pvecF i) * (starRingEnd ℂ z) ^ (qvecF i) *
        inner ℂ (Phi (split Ψ) z)
          ((fun i => KvecF f g BNH PHs E gHat0 i) i (Phi (split Ψ) z))) gauss :=
    MeasureTheory.integrable_finsetSum _ (fun i _ =>
      integrable_kafz_integrand (pvecF i) (qvecF i)
        ((fun i => KvecF f g BNH PHs E gHat0 i) i) (split Ψ))
  rw [bomb_eq_of_transport (s := Finset.range 25) (p := pvecF) (q := qvecF)
      (B := fun i => KvecF f g BNH PHs E gHat0 i) (W := H2ndF f g NH PHs E gHat0) hW Ψ,
    Kafz_sum (E := cfock (Excited m)) (s := Finset.range 25) (p := pvecF) (q := qvecF)
      (B := fun i => KvecF f g BNH PHs E gHat0 i) (split Ψ)]
  exact (integral_re hint).symm

end Work.BoseBoxFock
