import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.BGTZZFR
import Submission.Work.LinnikAreas.BGTZSetup

/-!
# The *capped* Deuring--Heilbronn repulsion

`Work.ZeroDensity.RepulsionWith c` is the Deuring--Heilbronn repulsion in the working region
(`|Im ρ| ≤ 1`) for **every** exceptional pair `(χ₁,β₁)` with `λ(β₁) ≤ 1/2`:

`∀ (χ,ρ) ≠ (χ₁,β₁),  zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → c·log(1/λ(β₁)) ≤ λ(ρ)`.

Its only known proofs (the fleet's `Work.LinnikAreas.repulsionWith_7_16`, via AREA 3's zero-free
table) have to deal with the *whole* range `λ₁ ≤ 1/2`, and it is exactly that part of the range
which forces the deep zero-free-region tables of AREA 3 (`ZeroFreeCert`) into AREA 6.

**The point of this file.**  AREA 6 never needs the repulsion in the whole range.  Both of its
consumers --- `Work.LinnikAreas.boxSumBound_of_inputs` (the box/rest-low/far-zero bookkeeping of
`LinnikAreas/area6.lean`) and `Work.LinnikAreas.siegelRestLow` (the working-region piece of the
Siegel zero sum) --- apply the repulsion to an exceptional pair whose `λ` is bounded by a
*constant they choose themselves* (`lamS ≤ 1/100` in `BoxSumBound`, and `lamS` is even smaller
inside `boxSumBound_of_inputs`, cf. the factor `exp(-(R+1)/c_r)`).  In the Siegel case of the
contract the exceptional pair is moreover supplied by `Work.LinnikContract.SiegelZero q lamS`
with that same internal `lamS`.

`RepulsionWithCap ε₀ c` records the repulsion with the *capped* hypothesis `λ(β₁) ≤ ε₀` instead of
`λ(β₁) ≤ 1/2`.  For `ε₀` small enough this is provable *without* AREA 3: with `λ(β₁) ≤ ε₀` the
exceptional pair is the pair of least `λ` in the working region, and that minimality follows from
the classical zero-free regions for `L(s,χ)` (`Commons.NumberTheory.DirichletCharacter.
LFunction_zeroFree_offAxis_uniform`, `…LFunction_zeroFree_uniform_realAxis`), Landau's repulsion of
two real zeros of distinct real characters (`OtherCharRepel.twoRealCharRepelProved`) and of two
zeros of one real character (`OtherCharRepel.twoRealZerosRepel`), and the `ζ` zero-free region near
the axis; the repulsion itself is then the proved BGTZ repulsion at all heights
(`Work.LinnikAreas.BGTZ.E.BGTZRepulsionGen_E`, `BGTZ.RepulsionGenC (11/5) (11/10) C₀`), whose
hypothesis `λ(ρ) ≥ λ(β₁)` is exactly that minimality.  See `LinnikAreas/RepulsionCap.lean`.
-/

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

/-- **The BGTZ repulsion at all heights** (`BGTZ.RepulsionGenC (11/5) (11/10) C₀` for the
constant `C₀ = max (1000/cZ) 1000` supplied by a uniform zero-free region `BGTZ.ZFRInputL cZ`),
stated *here* — verbatim as `Work.LinnikAreas.BGTZRepulsionGen` of
`LinnikAreas/area6Chain.lean` — so that the AREA 6 assembly
(`LinnikAreas/area6CapChain.lean`) and the frozen target (`LinnikAreas/area6.lean`) can use it
without the import chain `area6 ⟶ area6Chain ⟶ area6Final ⟶ area6Sound ⟶ area6`.  It is proved as
`Work.LinnikAreas.BGTZRepulsionGenE_proved` in `LinnikAreas/BGTZRepE.lean`. -/
def BGTZRepulsionGenE : Prop :=
  ∃ cZ : ℝ, 0 < cZ ∧ Work.LinnikAreas.BGTZ.ZFRInputL cZ ∧
    Work.LinnikAreas.BGTZ.RepulsionGenC (11 / 5) (11 / 10) (max (1000 / cZ) 1000)

/-- **The capped Deuring--Heilbronn repulsion.**  There is a threshold `q₀` such that for every
`q ≥ q₀`, every real `χ₁ ≠ 1` mod `q` with an exceptional real zero `β₁` of `λ(β₁) ≤ ε₀`, every
*other* pair `(χ,ρ)` of the working region (`zeroMult χ ρ ≠ 0`, `|Im ρ| ≤ 1`) satisfies
`c·log(1/λ(β₁)) ≤ λ(ρ)`. -/
def RepulsionWithCap (ε₀ c : ℝ) : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → Work.LinnikContract.zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    Work.LinnikContract.lamOf q (β₁ : ℂ) ≤ ε₀ →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      |ρ.im| ≤ 1 → ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      c * Real.log (1 / Work.LinnikContract.lamOf q (β₁ : ℂ)) ≤ Work.LinnikContract.lamOf q ρ

/-- The uncapped repulsion implies the capped one (a smaller range of `λ₁` is a weaker
statement). -/
theorem RepulsionWith.toCap {c ε₀ : ℝ} (hε : ε₀ ≤ 1 / 2)
    (h : Work.ZeroDensity.RepulsionWith c) : RepulsionWithCap ε₀ c := by
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨q₀, ?_⟩
  intro q hq hqne χ₁ β₁ hχ hsq hβ1 hz hle χ ρ hzρ him hne
  exact hq₀ q hq χ₁ β₁ hχ hsq hβ1 hz (le_trans hle hε) χ ρ hzρ him hne

/-- The capped repulsion is monotone in the cap. -/
theorem RepulsionWithCap.mono {ε₀ ε₀' c : ℝ} (hε : ε₀' ≤ ε₀) (h : RepulsionWithCap ε₀ c) :
    RepulsionWithCap ε₀' c := by
  obtain ⟨q₀, hq₀⟩ := h
  refine ⟨q₀, ?_⟩
  intro q hq hqne χ₁ β₁ hχ hsq hβ1 hz hle χ ρ hzρ him hne
  exact hq₀ q hq χ₁ β₁ hχ hsq hβ1 hz (le_trans hle hε) χ ρ hzρ him hne

end

end Work.LinnikAreas
