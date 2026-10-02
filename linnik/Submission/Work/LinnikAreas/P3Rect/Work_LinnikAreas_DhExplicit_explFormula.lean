import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_Inputs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_XiStrip
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_ZSBase
import Submission.Work.LinnikAreas.FarRepel.arithKthDeriv
import Submission.Work.LinnikAreas.tendsto_finsum_divisor_closedBall_mero
import Submission.Work.LinnikAreas.PrincipalZeroCount
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhKey
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_FarRepel_dhBasic

/-!
# The differentiated explicit formula (KNW (2.5)--(2.6))

We prove `Work.LinnikAreas.DhExplicit.ExplFormula`, the differentiated explicit formula of
Kadiri--Ng--Wong (arXiv:1902.08640, (2.5)--(2.6)) in the quadratic-field setting
`ζ_K = ζ · L(·,χ)` with a *real* primitive character `χ`, in the inequality form

`4 j (1 - β₁) / (c - 1)^{2j+1} ≥ ∑_u kMult χ u · W(u) - kMult χ β₁ · W(β₁)`,

where `W(u) = Re (1/(c-u)^{2j}) + Re (1/(c+iγ'-u)^{2j})`.

The analytic content (the Lagarias--Montgomery--Odlyzko partial-fraction expansion of
`(Ξ'/Ξ + Λ_χ'/Λ_χ)^{(2j-1)}` at the two points `s = c` and `s = c + iγ'`, the non-negativity of the
arithmetic side for real `χ`, the non-negativity of the trivial-zero contribution, and the
mean-value estimate comparing the pole at `1` with the exceptional zero `β₁`) is already available
in the workspace as the two-point bound

* `Work.LinnikAreas.FarRepel.dhKey` — the two-point zero sum is at most the two pole terms, and
* `Work.LinnikAreas.FarRepel.final_step` — the comparison with `β₁` and the `1`-pole.

What remains here, and is done in this file, is the *bookkeeping*: those two lemmas are stated for
the multiplicity

`multZ χ u = ord_u(Λ) + zeroMult χ u`   (`Λ = completedRiemannZeta`),

while `ExplFormula` uses

`kMult χ u = ord_u(Ξ) + ord_u(Λ_χ)`   (`Ξ = DhK.Xi`, `Λ_χ = completedLFunction χ`),

and the two-point weight is spelled there as `(1/(c-u))^{2j}` rather than `1/(c-u)^{2j}`.
The multiplicity functions agree pointwise:

* `ord_u(Ξ) = ord_u(Λ)`: `Ξ = (1/2) + (1/2) s (s-1) Λ₀(s)` agrees with `(1/2) s (s-1) Λ(s)` away
  from the poles `0, 1` of `Λ`, where the prefactor is analytic and non-zero, and at `0` and `1`
  both orders are `0` (there `Ξ ≠ 0` and `Λ` is not analytic);
* `zeroMult χ u = ord_u(Λ_χ)` for primitive `χ`
  (`Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive`).
-/

open scoped Classical BigOperators

namespace Work.LinnikAreas.DhExplicit

/-- **The vanishing order of `Ξ` equals that of the completed Riemann zeta function `Λ`.**
This is the `Λ`-version of `Work.LinnikAreas.analyticOrderNatAt_xiC_eq`: `Ξ` is definitionally the
entire completion `xiC = (1/2) + (1/2) s (s-1) Λ₀(s)`, so the identity away from the poles `0, 1`
transfers, and at `0` and `1` both orders vanish (`Ξ ≠ 0` there, `Λ` is not analytic there). -/
lemma explFormula_ordNatXi_eq_ordNatCompletedRiemannZeta (u : ℂ) :
    analyticOrderNatAt DhK.Xi u = analyticOrderNatAt completedRiemannZeta u := by
  by_cases h0 : u = 0
  · subst h0
    have hx : analyticOrderAt DhK.Xi 0 = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by rw [DhK.Xi_zero]; norm_num))
    have hX : analyticOrderNatAt DhK.Xi 0 = 0 := by simp [analyticOrderNatAt, hx]
    rw [hX,
      analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_zero]
  · by_cases h1 : u = 1
    · subst h1
      have hx : analyticOrderAt DhK.Xi 1 = 0 :=
        analyticOrderAt_eq_zero.mpr (Or.inr (by rw [Xi_one]; norm_num))
      have hX : analyticOrderNatAt DhK.Xi 1 = 0 := by simp [analyticOrderNatAt, hx]
      rw [hX,
        analyticOrderNatAt_of_not_analyticAt Work.LinnikAreas.not_analyticAt_completedZeta_one]
    · rw [show DhK.Xi = Work.LinnikAreas.xiC from rfl]
      exact Work.LinnikAreas.analyticOrderNatAt_xiC_eq u h0 h1

/-- **The two spellings of the zero multiplicity of `ζ_K` agree.**  For a primitive character `χ`,
`multZ χ u = ord_u(Λ) + zeroMult χ u` (the multiplicity used by the Deuring--Heilbronn assembly of
`Work.LinnikAreas.FarRepel`) equals `kMult χ u = ord_u(Ξ) + ord_u(Λ_χ)` (the multiplicity of
`Work.LinnikAreas.DhK`). -/
lemma explFormula_multZ_eq_kMult {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (u : ℂ) :
    Work.LinnikAreas.FarRepel.multZ χ u = DhK.kMult χ u := by
  rw [Work.LinnikAreas.FarRepel.multZ, DhK.kMult,
    explFormula_ordNatXi_eq_ordNatCompletedRiemannZeta u,
    Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive χ hprim u]

/-- **The two spellings of the two-point weight agree.**  The weight `Wt` of
`Work.LinnikAreas.FarRepel` is written with `(1/(c-u))^{2j}`, the one in `ExplFormula` with
`1/(c-u)^{2j}`; these are the same by `one_div_pow`. -/
lemma explFormula_Wt_eq (c γ' : ℝ) (j : ℕ) (u : ℂ) :
    Work.LinnikAreas.FarRepel.Wt c γ' j u
      = (1 / ((c : ℂ) - u) ^ (2 * j)).re
        + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re := by
  rw [Work.LinnikAreas.FarRepel.Wt, one_div_pow, one_div_pow]

/-- **The differentiated explicit formula (KNW (2.5)--(2.6)).**  The two-point bound
`Work.LinnikAreas.FarRepel.dhKey` (the partial-fraction expansion of the `(2j-1)`-st derivative of
`Ξ'/Ξ + Λ_χ'/Λ_χ`, evaluated at `c` and at `c + iγ'`: the trivial-zero and arithmetic
contributions are `≥ 0`, so the zero sum is bounded by the two pole terms) combined with the
endgame `Work.LinnikAreas.FarRepel.final_step` (the exceptional real zero `β₁` is subtracted and the
difference against the pole at `1` is estimated by `4 j (1-β₁)/(c-1)^{2j+1}`) gives the inequality
for the multiplicity `multZ χ u = ord_u(Λ) + zeroMult χ u`; the last two steps convert it to the
multiplicity `kMult χ u = ord_u(Ξ) + ord_u(Λ_χ)` of the statement by the pointwise agreement of the
multiplicities and of the two spellings of the weight.

The parity of `χ` only enters through the position of the trivial zeros of `L(·,χ)`
(`a = 0` for even, `a = 1` for odd `χ`), so the proof splits into those two cases; there is no
threshold on the conductor here, hence the statement holds with `q₀ = 0`. -/
theorem explFormula : Work.LinnikAreas.DhExplicit.ExplFormula := by
  refine ⟨0, ?_⟩
  intro q _hq _hqne χ hχ hprim hχ2 j hj c γ' hc β₁ hβ₁ hz₁
  have hc1 : (1 : ℝ) < c := by linarith
  have hK : ∀ u : ℂ, (Work.LinnikAreas.FarRepel.multZ χ u : ℝ)
      = ((DhK.kMult χ u : ℕ) : ℝ) := fun u => by rw [explFormula_multZ_eq_kMult χ hprim u]
  have hW := explFormula_Wt_eq c γ' j
  rcases χ.even_or_odd with hev | hod
  · obtain ⟨hsumm, hkey⟩ := Work.LinnikAreas.FarRepel.dhKey χ hχ hprim hχ2 j hj 0
      (fun _ => rfl) (fun ho => absurd (hev.symm.trans ho) (by norm_num)) hc1
    have hfin := Work.LinnikAreas.FarRepel.final_step χ hχ hprim hc hβ₁ hz₁ hsumm hkey
    refine ⟨hsumm.congr (fun u => by rw [hK u, hW u]), ?_⟩
    have hsum_eq : (∑' u : ℂ, (Work.LinnikAreas.FarRepel.multZ χ u : ℝ)
          * Work.LinnikAreas.FarRepel.Wt c γ' j u)
        = ∑' u : ℂ, ((DhK.kMult χ u : ℕ) : ℝ)
          * ((1 / ((c : ℂ) - u) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re) :=
      tsum_congr (fun u => by rw [hK u, hW u])
    rw [hsum_eq, hK (β₁ : ℂ), hW (β₁ : ℂ)] at hfin
    exact hfin
  · obtain ⟨hsumm, hkey⟩ := Work.LinnikAreas.FarRepel.dhKey χ hχ hprim hχ2 j hj 1
      (fun he => absurd (he.symm.trans hod) (by norm_num)) (fun _ => rfl) hc1
    have hfin := Work.LinnikAreas.FarRepel.final_step χ hχ hprim hc hβ₁ hz₁ hsumm hkey
    refine ⟨hsumm.congr (fun u => by rw [hK u, hW u]), ?_⟩
    have hsum_eq : (∑' u : ℂ, (Work.LinnikAreas.FarRepel.multZ χ u : ℝ)
          * Work.LinnikAreas.FarRepel.Wt c γ' j u)
        = ∑' u : ℂ, ((DhK.kMult χ u : ℕ) : ℝ)
          * ((1 / ((c : ℂ) - u) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - u) ^ (2 * j)).re) :=
      tsum_congr (fun u => by rw [hK u, hW u])
    rw [hsum_eq, hK (β₁ : ℂ), hW (β₁ : ℂ)] at hfin
    exact hfin

end Work.LinnikAreas.DhExplicit
