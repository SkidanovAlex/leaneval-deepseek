import Mathlib
import Submission.Work.LayerCont.SplitPoint
import Submission.Work.Asymptotics.rectInt_eq_residue
import Submission.Work.Residues.ResidueSecondVariable
import Submission.Work.LayerCont.Right.Defs
import Submission.Work.LayerCont.Arc.Defs
import Submission.Work.LayerCont.FarTail.CuspFar
import Submission.Work.Asymptotics.CuspDecay.Regimes
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.HatLayer
import Submission.Work.CKFinal.LineDecay.LineAssembly
import Submission.Work.CKFinal.LineDecay.P1_line_bound_eight
import Submission.Work.CKFinal.LineDecay.P1_line_bound_twentyfour
import Submission.Work.CKFinal.LineDecay.P2_line_bound_eight
import Submission.Work.CKFinal.LineDecay.P2_line_bound_twentyfour
import Submission.Work.CKFinal.LineDecay.P3_line_bound_eight
import Submission.Work.CKFinal.LineDecay.P3_line_bound_twentyfour
import Submission.Work.CKFinal.LineDecay.AllIdentities

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

# layer_line_decay  (namespace Work.CKFinal)  — (f), part 3b: decay of F and F̃ on Re τ = ±1/2

Statement: for τ = x₀ + iy, x₀ = ±1/2, y ≥ Y₀, all r:
 |gaussTerm τ r + pL(τ,r)| and |pL(S•τ, r)·τ^{−d/2}| are ≤ C y^N e^{−μ y}, μ = π (d=8), 3π (d=24).
(These are F(τ,r) and −F̃(τ,r) once F₂ = pL on 𝒟: τ, S•τ ∈ 𝒟 for y large.)

Math (CKMRV §5.2 (5.12), specialised to the two lines where no near-pole occurs):
H := 1, split point p = H (`Work.LayerCont.layerAt_eq_paperLayer`, SplitPoint.lean):
pL = layerLowAt H + layerTruncAt H + highPartAt H. Let A(τ,w) := G₀₀ + wG₀₁ + e^{−2πiw}(G₁₀ + wG₁₁)
(so Aexp(τ,t) = A(τ,it)); sinSqC r = 2 − e^{iπr²} − e^{−iπr²}. Then
 layerTruncAt H = −i Σ_{ε∈{0,±1}} c_ε ∫_{ε+iH}^{ε+i∞} (K − A)(τ, w−ε) e^{iπr²w} dw, c₀ = 2, c_{±1} = −1.
Shift the ε = ±1 rays to Re w = 0 through the half-strips Q_ε = {Re w between 0 and ε, Im w ≥ H}
(rectangles with top edge → ∞: `Work.Asymptotics.rectInt_eq_residue`; the top edge vanishes because
(K − A)(τ,w) = O(poly·e^{−π Im w}) for Im w ≥ y+1, `FarTail.cusp_expansion_of_kernel_of_clean`).
Poles of w ↦ K(τ,w−ε) in Q_ε (y ≥ 2 ⇒ the only orbit points of τ with Im ≥ 1 are τ+ℤ): exactly one;
x₀ = 1/2: w = τ ∈ Q₊₁ (z = τ−1, Res = 1/(2π), `Work.Residues.hasResidue_Kfun_second`) and w = τ−1 ∈ Q₋₁
(z = τ, Res 0); x₀ = −1/2 symmetric (z = τ+1, Res −1/(2π), `Right.hasResidue_Kfun_tauAddOne`). The
residue term is exactly −gaussTerm τ r (sign: cross-check with far_identity_data's +sinSqC·resCorr).
Result: g + pL = P₁ + P₂ + P₃ + P₄ with
 P₁ = layerLowAt H = sinSqC ∫_0^H K(τ,it)e^{−πr²t}dt,
 P₂ = −i Σ_{ε=±1} c_ε ∫_{[iH, ε+iH]} K(τ, w−ε) e^{iπr²w} dw   (horizontal segments),
 P₃ = −i ∫_{iH}^{i∞} Φ(τ,w) e^{iπr²w} dw,  Φ(τ,w) = 2K(τ,w) − K(τ,w−1) − K(τ,w+1)
      (A drops out: A(τ,·) is affine×1-periodic, killed by the second difference),
 P₄ = highPartAt H − i Σ_{ε=±1} c_ε ∫_{[iH, ε+iH]} A(τ, w−ε) e^{iπr²w} dw ≡ 0
      (elementary: both are the regularised value of sinSqC ∫_H^∞ A e^{−πr²t}; verify by direct
      integration of w^j e^{2πikw}e^{iπr²w} and the psi1 closed form, or for r² > 2 by the same
      contour shift of the entire A, then all r by `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).
Bounds from kernel_S_bound, writing K(τ,z) = (K|^zS)(τ, S•z)·(S•z)^{2−d/2} and
Φ(τ,·) = 2(K̂|^zS)(τ,·) (CKMRV: K|^z(T+T⁻¹−2) = K₊|^zS − K₋|^zS; needs the z-variable ideal
relations — check Residues/ and Kernels/ for `KPlus_slash_z`-type lemmas, else derive from the
cleared-kernel formulas), plus the denominator bound at Re τ = ±1/2, Re z = 0:
|Δ(τ)Δ(z)(jτ − jz)| ≥ c·max(e^{−2π Im τ}, e^{−2π Im z}) (here e^{2πiτ} = −e^{−2πy} < 0 < e^{2πiz},
so NO window cancellation; template `CuspDecay.DOne_lower_fst/_snd` (CuspDecay/Regimes.lean)):
 P₃ ≤ C poly·e^{−πn̂y}∫_H^∞ e^{−πt}min(e^{2πy},e^{2πt})dt ≤ C poly·e^{−π(n̂−1)y};
 P₁ likewise with z' = S•(it) = i/t; P₂: Im(S•z) ≥ 1/2, |Δ(τ)(jτ − jz)| ≥ c ⇒ ≤ C poly·e^{−πn̂y}.
n̂ − 1 = 1 (d=8), 3 (d=24). Uniform in r since |e^{iπr²w}| ≤ 1 for Im w ≥ 0 and |sinSqC r| ≤ 4
for real r.
F̃ part: `Work.LayerCont.Arc.Kaxis_Kfun_S_smul` (K(S•σ,it) = −σ^{d/2}K̂(σ,it)); define
Ĝᵢⱼ(σ) := −σ^{−d/2}Gcusp ℓ d i j (S•σ), so pL(S•σ) = −σ^{d/2}·pL̂(σ) where pL̂ is paperLayer's formula
with K̂ and Ĝ (the `highPart`/`Aexp` defs are generic in G). Repeat the computation: all residues of
K̂(σ,·) at σ, σ±1 vanish (`Work.Residues.hasResidue_Khat_second`; diagonal: `hasResidue_KPlus_self`,
`hasResidue_KMinus_self`), so no gaussTerm appears; Φ̂ = 2(K|^zS) ⇒ same bounds.

--imports: Submission.Work.LayerCont.SplitPoint Submission.Work.Asymptotics.rectInt_eq_residue Submission.Work.Residues.ResidueSecondVariable Submission.Work.LayerCont.Right.Defs Submission.Work.LayerCont.Arc.Defs Submission.Work.LayerCont.FarTail.CuspFar Submission.Work.Asymptotics.CuspDecay.Regimes (+ kernel_S_bound)
-/

namespace Work.CKFinal

/-- **Assembly of `layer_line_decay` from its four inputs**: the two all-`r` contour-shift
identities (one per dimension, for both kernels) and the three bound families in each dimension.
The `P₃` bounds are kept as hypotheses here only so that this reduction can be formalised before
the siblings land; the final `layer_line_decay` feeds in `P3_line_bound_eight`,
`P3_line_bound_twentyfour` and `shift_identity_dshift`. -/
theorem layer_line_decay_assembly (ℓ : Work.Kernels.LogLambdaData)
    (hP3e8 : ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P3 (Work.Kernels.Khat ℓ 8) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(Real.pi * τ.im))))
    (hP3e24 : ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))
          ∧ ‖Work.CKFinal.P3 (Work.Kernels.Khat ℓ 24) r τ‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))))
    (hid8 : ∀ (τ : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 12 ≤ τ.im →
      ((∀ r : ℝ, Work.Kernels.gaussTerm τ r
          + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 8) ℓ 8 τ r
          = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ 8) r τ
            + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ 8) r τ
            + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 8) r τ)
        ∧ (∀ r : ℝ, Work.CKFinal.paperLayerK (Work.Kernels.Khat ℓ 8) (Work.CKFinal.Ghat ℓ 8) r τ
          = Work.CKFinal.P1 (Work.Kernels.Khat ℓ 8) r τ
            + Work.CKFinal.P2 (Work.Kernels.Khat ℓ 8) r τ
            + Work.CKFinal.P3 (Work.Kernels.Khat ℓ 8) r τ)))
    (hid24 : ∀ (τ : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 12 ≤ τ.im →
      ((∀ r : ℝ, Work.Kernels.gaussTerm τ r
          + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 τ r
          = Work.CKFinal.P1 (Work.Kernels.Kfun ℓ 24) r τ
            + Work.CKFinal.P2 (Work.Kernels.Kfun ℓ 24) r τ
            + Work.CKFinal.P3 (Work.Kernels.Kfun ℓ 24) r τ)
        ∧ (∀ r : ℝ, Work.CKFinal.paperLayerK (Work.Kernels.Khat ℓ 24) (Work.CKFinal.Ghat ℓ 24) r τ
          = Work.CKFinal.P1 (Work.Kernels.Khat ℓ 24) r τ
            + Work.CKFinal.P2 (Work.Kernels.Khat ℓ 24) r τ
            + Work.CKFinal.P3 (Work.Kernels.Khat ℓ 24) r τ)))
    (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        ‖Work.Kernels.gaussTerm τ r
            + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r‖
          ≤ C * τ.im ^ N * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)) ∧
        ‖Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
            (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))‖
          ≤ C * τ.im ^ N * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)) := by
  rcases hd with h8 | h24
  · subst h8
    rw [if_pos rfl]
    exact Work.CKFinal.line_decay_of_identity ℓ 8 (Or.inl rfl) Real.pi hid8
      (Work.CKFinal.LineDecay.P1_line_bound_eight ℓ)
      (Work.CKFinal.LineDecay.P2_line_bound_eight ℓ) hP3e8
  · subst h24
    rw [if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
    exact Work.CKFinal.line_decay_of_identity ℓ 24 (Or.inr rfl) (3 * Real.pi) hid24
      (Work.CKFinal.LineDecay.P1_line_bound_twentyfour ℓ)
      (Work.CKFinal.LineDecay.P2_line_bound_twentyfour ℓ) hP3e24

/-- The cusp-`∞` decay of `F = gaussTerm + paperLayer` and of `F̃ = -τ^{-d/2} paperLayer(S•τ)`
along the two vertical lines `Re τ = ±1/2`, uniformly in `r`: rate `e^{-π Im τ}` for `d = 8`
and `e^{-3π Im τ}` for `d = 24` (CKMRV (4.2toshow2)/(4.2toshow3) on these lines). -/
theorem layer_line_decay (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        ‖Work.Kernels.gaussTerm τ r
            + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r‖
          ≤ C * τ.im ^ N * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)) ∧
        ‖Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
            (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))‖
          ≤ C * τ.im ^ N * Real.exp (-((if d = 8 then Real.pi else 3 * Real.pi) * τ.im)) :=
  layer_line_decay_assembly ℓ
    (Work.CKFinal.LineDecay.P3_line_bound_eight ℓ)
    (Work.CKFinal.LineDecay.P3_line_bound_twentyfour ℓ)
    (fun τ hline hy =>
      Work.CKFinal.LineDecay.all_identities_route1 ℓ 8 (Or.inl rfl) τ hline hy)
    (fun τ hline hy =>
      Work.CKFinal.LineDecay.all_identities_route1 ℓ 24 (Or.inr rfl) τ hline hy)
    d hd

end Work.CKFinal
