import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.SymSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SymBlocks` — the word blocks of the `symR`/`KzOpC` discrepancy

`symDiscrep` (`Submission/Work/BoseBoxFock/symDiscrep.lean`) is proved by normalising
both sides of

    symR r − KzOpC (r²/ℓ³) = r²•D2F + r•D1F + D0F

into a ℂ-linear combination of a fixed list of *word blocks*.  A block is a single
lattice sum `Σ_k w_k • (word at k)` whose weight is k-independent.  The blocks used
are:

* `Bkin f E = Σ_k τ(k) nmF f k`, `nPlusChi f` (both already in the corpus) and the two
  new number blocks `BNW`, `BNω` (weight `Ŵ₁(k)` resp. `Ŵ₁ω(k)`);
* the pairing blocks `BPa`, `BPc` (weight `Ŵ₁(k)` against `a_k a_{−k}` resp.
  `a_k†a_{−k}†`);
* the `χ̂`-linear blocks `BchiC Finset.univ E.hatChi 1 f`, `BchiA Finset.univ E.hatChi 1 f`
  and the `χ̂²`-linear blocks `BchiC (excited Mode) E.hatChiSq 1 g`,
  `BchiA (excited Mode) E.hatChiSq 1 g`;
* the cubic blocks `BQ3a`/`BQ3b` with the *unweighted* kernel `f_L(s) Ŵ₁(k)`;
* the single word `nmF f 0` (the `k = 0` number word) and the identity `1`.

The normalisation replaces "fusing the many lattice sums of the expansion" by
*monomial splitting* (`SymSum.sum_add_smul_split`): every occurrence is rewritten as a
linear combination of these blocks with *k-independent scalar coefficients*, and the
two sides are then matched by scalar arithmetic (`module`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-- Number block: `Σ_k Ŵ₁(k) a_k†a_k` (on the spectator space). -/
noncomputable def BNW {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.W1 k : ℝ) : ℂ) • nmF f k

/-- Number block: `Σ_k Ŵ₁ω(k) a_k†a_k`. -/
noncomputable def BNω {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.W1omega k : ℝ) : ℂ) • nmF f k

/-- Pairing block: `Σ_k Ŵ₁(k) a_k a_{−k}`. -/
noncomputable def BPa {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.W1 k : ℝ) : ℂ) • ((annOfE (f k)).comp (annOfE (f (-k))))

/-- Pairing block: `Σ_k Ŵ₁(k) a_k†a_{−k}†`. -/
noncomputable def BPc {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  ∑ k : Mode, ((E.W1 k : ℝ) : ℂ) • ((creOfE (f k)).comp (creOfE (f (-k))))

/-- `χ̂`-linear block (creation part): `Σ_{k} χ̂_k a_k†` over the full lattice. -/
noncomputable def BχC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Finset.univ : Finset Mode) E.hatChi 1 f

/-- `χ̂`-linear block (annihilation part): `Σ_{k} χ̂_k a_k`. -/
noncomputable def BχA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Finset.univ : Finset Mode) E.hatChi 1 f

/-- `χ̂²`-linear block (creation part): `Σ_{s ≠ 0} χ̂²_s ã_s†`. -/
noncomputable def BchiSqC {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiC (Work.BoseB7.excited Mode) E.hatChiSq 1 g

/-- `χ̂²`-linear block (annihilation part): `Σ_{s ≠ 0} χ̂²_s ã_s`. -/
noncomputable def BchiSqA {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (g : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BchiA (Work.BoseB7.excited Mode) E.hatChiSq 1 g

/-- The cubic `Q̃₃` block with the *unweighted* kernel `f_L(s) Ŵ₁(k)`. -/
noncomputable def BQa {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BQ3a (Work.BoseB7.excited Mode) PHs (fun s k => E.fL s * E.W1 k) g f

/-- The adjoint cubic `Q̃₃` block with the unweighted kernel. -/
noncomputable def BQb {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode) :
    cfock (Excited m) →ₗ[ℂ] cfock (Excited m) :=
  BQ3b (Work.BoseB7.excited Mode) PHs (fun s k => E.fL s * E.W1 k) g f

/-- Pulling a constant factor out of the `BchiC` kernel. -/
theorem BchiC_const {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ) (φ : Mode → Fin m → ℝ) :
    BchiC s χ c φ = (c : ℂ) • BchiC s χ 1 φ := by
  simp only [BchiC, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- Pulling a constant factor out of the `BchiA` kernel. -/
theorem BchiA_const {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (s : Finset Mode) (χ : Mode → ℝ) (c : ℝ) (φ : Mode → Fin m → ℝ) :
    BchiA s χ c φ = (c : ℂ) • BchiA s χ 1 φ := by
  simp only [BchiA, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- Pulling a *constant* factor out of the `BQ3a` kernel (constant in both indices). -/
theorem BQ3a_const {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (c : ℝ) (g f : Mode → Fin m → ℝ) :
    BQ3a S Ks (fun s k => c * γ s k) g f = (c : ℂ) • BQ3a S Ks γ g f := by
  simp only [BQ3a]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-- Pulling a *constant* factor out of the `BQ3b` kernel (constant in both indices). -/
theorem BQ3b_const {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (S Ks : Finset Mode) (γ : Mode → Mode → ℝ) (c : ℝ) (g f : Mode → Fin m → ℝ) :
    BQ3b S Ks (fun s k => c * γ s k) g f = (c : ℂ) • BQ3b S Ks γ g f := by
  simp only [BQ3b]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_smul]
  congr 1
  push_cast
  ring

/-! ## Elementary block identities (definitional unfoldings of the corpus words) -/

/-- `Bkin` is the block `Σ_k τ(k) a_k†a_k`. -/
theorem Bkin_eq_block {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bkin f E = ∑ k : Mode, ((E.tau k : ℝ) : ℂ) • nmF f k := rfl

/-- The gap spectator is the excited number block `nPlusChi`. -/
theorem Bgap_eq_nPlusC :
    (Bgap (m := m)) = nPlusC (m := m) := rfl

/-- `BW` with the `(Ŵ₁ + Ŵ₁ω)` weight splits into the two monomial blocks. -/
theorem BW_split {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    BW (Finset.univ : Finset Mode) (fun k => E.W1 k + E.W1omega k) f
      = BNW f E + BNω f E := by
  simp only [BW, BNW, BNω]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Complex.ofReal_add]
  exact add_smul _ _ _

/-- `BW` with weight `1` is the excited number block. -/
theorem BW_one {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) :
    BW (Finset.univ : Finset Mode) (fun _ => (1 : ℝ)) f = nPlusChi f := by
  simp only [BW, nPlusChi, nOpC, nmF, Complex.ofReal_one, one_smul]

/-- The Bogoliubov pairing word `a_k a_{−k}` is the block `BPa`. -/
theorem Bbog1_eq_BPa {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bbog1 (Finset.univ : Finset Mode) (fun k => E.W1 k) f = BPa f E := rfl

/-- The adjoint pairing word `a_k†a_{−k}†` is the block `BPc`. -/
theorem Bbog2_eq_BPc {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (f : Mode → Fin m → ℝ) (E : Work.BoseB7.Q3Env Mode) :
    Bbog2 (Finset.univ : Finset Mode) (fun k => E.W1 k) f = BPc f E := rfl

end Work.BoseBoxFock
