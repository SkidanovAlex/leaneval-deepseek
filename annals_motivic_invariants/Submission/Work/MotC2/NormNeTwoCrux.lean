import Mathlib
import Submission.Work.MotC2.NeTwoSetup
import Submission.Work.MotC2.NeTwoRatFuncSqMul
import Submission.Work.MotC2.NeTwoSquarefreeCubic
import Submission.Work.MotC2.Negation
import Submission.Work.MotC2.NeTwoRatFuncCrux
import Submission.Work.MotC2.NeTwoSquarefreeD

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

variable {L : Type*} [Field L]

/-- `eK E` is the image of `linCoef E = a₁X + a₃` under `xPhi`. -/
lemma linCoef_xPhi (E : WeierstrassCurve L) : xPhi E (linCoef E) = eK E := by
  simp [xPhi, eK, linCoef]

/-- `cK E` is the image of `cubCoef E = X³ + a₂X² + a₄X + a₆` under `xPhi`. -/
lemma cubCoef_xPhi (E : WeierstrassCurve L) : xPhi E (cubCoef E) = cK E := by
  simp [xPhi, cK, cubCoef]

/-- **The crux for `n = 3` in characteristic `≠ 2`.**  Let `E` be an elliptic Weierstrass curve over
a field `L` with `(2 : L) ≠ 0`, and let `p, q ∈ L(x) = range (xPsi E)` satisfy

* `2 * p - q * e ∈ L[x]` (the trace of `p + q·y`),
* `p ^ 2 - p * q * e - q ^ 2 * c ∈ L[x]` (its norm),

where `e = eK E = a₁x + a₃` and `c = cK E = x³ + a₂x² + a₄x + a₆`.  Then `p, q ∈ L[x]`.

Transfer everything to `L(X) = RatFunc L` along the injection `xPsi E` (whose range is the subfield
`L(x)`): with `p = xPsi p₀`, `q = xPsi q₀`, `e := linCoef E`, `c := cubCoef E`, the two hypotheses
read `2 p₀ - q₀ ē ∈ L[X]` and `p₀² - p₀ q₀ ē - q₀² c̄ ∈ L[X]`, and `Work.MotC2.NeTwoRatFuncCrux`
(same directory) gives `p₀, q₀ ∈ L[X]`.  Its hypothesis `Squarefree (linCoef E ^ 2 + 4 * cubCoef E)`
is `Work.MotC2.NeTwoSquarefreeD`: the polynomial `linCoef E ^ 2 + 4 * cubCoef E` is the classical
2-torsion cubic `4x³ + b₂x² + 2b₄x + b₆`, and a repeated root of it would give a singular point
`(α, -(a₁α + a₃)/2)` of the elliptic curve `E`. -/
theorem NormNeTwoCrux (L : Type*) [Field L] (E : WeierstrassCurve L) [E.IsElliptic]
    (h2 : (2 : L) ≠ 0) (p q : Work.MotC2.Func E)
    (hp : p ∈ Set.range (Work.MotC2.xPsi E)) (hq : q ∈ Set.range (Work.MotC2.xPsi E))
    (hT : 2 * p - q * Work.MotC2.eK E ∈ Work.MotC2.Ax E)
    (hN : p ^ 2 - p * (q * Work.MotC2.eK E) - q ^ 2 * Work.MotC2.cK E ∈ Work.MotC2.Ax E) :
    p ∈ Work.MotC2.Ax E ∧ q ∈ Work.MotC2.Ax E := by
  obtain ⟨p₀, rfl⟩ := hp
  obtain ⟨q₀, rfl⟩ := hq
  -- the two hypotheses, as memberships of elements of `L(x) = range (xPsi E)`
  have hT' : 2 * xPsi E p₀ - xPsi E q₀ * eK E ∈ (xPhi E).range := by
    rw [xPhi_range E]; exact hT
  have hN' : xPsi E p₀ ^ 2 - xPsi E p₀ * (xPsi E q₀ * eK E) - xPsi E q₀ ^ 2 * cK E ∈
      (xPhi E).range := by
    rw [xPhi_range E]; exact hN
  -- the corresponding polynomials in `L(x) = range (xPhi E) ⊆ L(E)`
  obtain ⟨T, hTp⟩ := (AlgHom.mem_range (xPhi E)).mp hT'
  obtain ⟨N, hNp⟩ := (AlgHom.mem_range (xPhi E)).mp hN'
  -- descend along the injection `L(X) → L(x)`
  have hTR : 2 * p₀ - q₀ * algebraMap (Polynomial L) (RatFunc L) (linCoef E) =
      algebraMap (Polynomial L) (RatFunc L) T := by
    apply xPsi_injective E
    simp only [map_sub, map_mul, map_ofNat, xPsi_apply_algebraMap, linCoef_xPhi]
    exact hTp.symm
  have hNR : p₀ ^ 2 - p₀ * (q₀ * algebraMap (Polynomial L) (RatFunc L) (linCoef E)) -
      q₀ ^ 2 * algebraMap (Polynomial L) (RatFunc L) (cubCoef E) =
      algebraMap (Polynomial L) (RatFunc L) N := by
    apply xPsi_injective E
    simp only [map_sub, map_mul, map_pow, xPsi_apply_algebraMap, linCoef_xPhi, cubCoef_xPhi]
    exact hNp.symm
  -- the crux over `L(X)`, with the squarefree 2-torsion cubic
  have hd : Squarefree (linCoef E ^ 2 + 4 * cubCoef E) := NeTwoSquarefreeD L E h2
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ :=
    NeTwoRatFuncCrux L h2 (linCoef E) (cubCoef E) hd p₀ q₀ ⟨T, hTR.symm⟩ ⟨N, hNR.symm⟩
  -- conclude: `p = xPhi P` and `q = xPhi Q` lie in `L[x]`
  refine ⟨?_, ?_⟩
  · rw [← hP, xPsi_apply_algebraMap]
    exact xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨P, rfl⟩
  · rw [← hQ, xPsi_apply_algebraMap]
    exact xPhi_range E ▸ (AlgHom.mem_range (xPhi E)).mpr ⟨Q, rfl⟩

end Work.MotC2
