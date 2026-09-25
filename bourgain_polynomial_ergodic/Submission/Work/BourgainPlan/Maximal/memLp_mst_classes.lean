import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols

/-!
# The `L^∞(𝕋)`-classes of the MST major-arc symbols

`mstNu P l d χ η n` (the level-`n` major-arc model `ν_{2^n}`) and `mstNuS P l d χ η n s` (its
level-`s` piece `ν_{2^n}^s`) are *finite* sums of scalar multiples of translates of the single
function `Φ_{2^n}(· - β) · η_s(· - β)`, weighted by the complete sums `G(β)`.  Hence they are a.e.
bounded on the circle as soon as that single function is, which is immediate from the a.e.
boundedness of the profile `mstProf P (2^n)` and of the bump `mstEta d χ η s`
(`memLp_mst_symbols`), the latter of which needs only the continuity of `η` — no support,
normalisation or size hypothesis.  The analytic estimates of MST §4–§5 consume exactly this
`MemLp ⊤`-membership as a side condition (to form the `L^∞` multiplier classes `mstNuCls`,
`mstNuSCls`), so we collect all three families here.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

set_option autoImplicit false

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle
local notation "haarT" => (AddCircle.haarAddCircle (T := 1))

/-- **The level bump `η_n` is `L^∞` on the circle** for every continuous `η` and every level `n`:
`η_n = η(c_n · iwRep)` is the fundamental-domain lift of a continuous `ℝ`-function, hence a.e.
bounded (`memLp_mst_symbols`).  No hypothesis on the size of the scaling factor `c_n` is needed. -/
lemma memLp_mstEta_of_continuous (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη : Continuous η) (n : ℕ) : MeasureTheory.MemLp (mstEta d χ η n) ⊤ haarT :=
  (memLp_mst_symbols P (2 ^ n) ((2 : ℝ) ^ ((n : ℝ) * ((d : ℝ) - χ))) η hη).2.2

/-- **The profile `Φ_N` is `L^∞` on the circle** (`memLp_mst_symbols`). -/
lemma memLp_mstProf_symbol (P : Polynomial ℤ) (N : ℕ) :
    MeasureTheory.MemLp (mstProf P N) ⊤ haarT :=
  (memLp_mst_symbols P N 0 (fun _ : ℝ => (0 : ℂ)) continuous_const).2.1

/-- **The major-arc model symbol over a finite arc set is `L^∞`** as soon as the
profile-times-bump function `Φ · ψ` is: `mstModelFn G Φ ψ Es` is the finite sum
`Σ_{β ∈ Es} G β · (Φ · ψ)(· - β)`, and a translate of an a.e. bounded function is a.e. bounded
(`memLp_arcTranslate`).  The weights `G β` may be arbitrary complex numbers. -/
lemma memLp_mstModelFn_of {G Φ ψ : Circ → ℂ} {Es : Finset Circ}
    (h : MeasureTheory.MemLp (fun ζ : Circ => Φ ζ * ψ ζ) ⊤ haarT) :
    MeasureTheory.MemLp (mstModelFn G Φ ψ Es) ⊤ haarT :=
  memLp_arcSymbolW (θ := fun β : Circ => β) (w := G) (s := Es)
    (φ := fun ζ : Circ => Φ ζ * ψ ζ) h

theorem memLp_mst_classes (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hη : Continuous η) :
    (∀ n : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstNu P l d χ η n) ⊤
        (AddCircle.haarAddCircle (T := 1))) ∧
    (∀ n s : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstNuS P l d χ η n s) ⊤
        (AddCircle.haarAddCircle (T := 1))) ∧
    (∀ n : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstEta d χ η n) ⊤
        (AddCircle.haarAddCircle (T := 1))) := by
  have hEta : ∀ n : ℕ, MeasureTheory.MemLp (mstEta d χ η n) ⊤ haarT :=
    fun n => memLp_mstEta_of_continuous P d χ η hη n
  have hProf : ∀ n : ℕ, MeasureTheory.MemLp (mstProf P (2 ^ n)) ⊤ haarT :=
    fun n => memLp_mstProf_symbol P (2 ^ n)
  refine ⟨fun n => ?_, fun n s => ?_, fun n => hEta n⟩
  · -- `ν_{2^n}`: the level-`n` profile times the level-`n` bump, over the arc set `𝒰(n)`
    have hcomb : MeasureTheory.MemLp (star (mstProf P (2 ^ n)) * mstEta d χ η n) ⊤ haarT :=
      (hProf n).star.mul (hEta n)
    have hmain := memLp_mstModelFn_of (G := fun β : Circ => star (mstG P β))
      (Φ := fun ζ : Circ => star (mstProf P (2 ^ n) ζ)) (ψ := mstEta d χ η n)
      (Es := mstU l n) hcomb
    simpa only [mstNu] using hmain
  · -- `ν_{2^n}^s`: the level-`n` profile times the *level-`s`* bump, over `𝒰(s+1) ∖ 𝒰(s)`
    have hcomb : MeasureTheory.MemLp (star (mstProf P (2 ^ n)) * mstEta d χ η s) ⊤ haarT :=
      (hProf n).star.mul (hEta s)
    have hmain := memLp_mstModelFn_of (G := fun β : Circ => star (mstG P β))
      (Φ := fun ζ : Circ => star (mstProf P (2 ^ n) ζ)) (ψ := mstEta d χ η s)
      (Es := mstLevel l (s + 1) \ mstLevel l s) hcomb
    simpa only [mstNuS] using hmain

end

end Work.BourgainPlan.Maximal
