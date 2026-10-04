import Mathlib
import Submission.Work.Diff.Alg.Pinch.ChatShiftDefs
import Submission.Work.Diff.Alg.Pinch.Chat_margin
import Submission.Work.Diff.Alg.Pinch.Linv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Work.Diff.Alg.Pinch

/-- **The Böhm–Wilking inverse of a tensor shifted by a multiple of the round sphere.**

`linv a' b'` is the explicit inverse of the Böhm–Wilking transform `ell a' b'`
(`Work.Diff.Alg.Pinch.linv`, `ell`).  For an algebraic curvature tensor `S` one has
`ell a' b' (linv a' b' (ell a b S + t • Iso n)) = ell a b S + t • Iso n`, and the point of this
statement is that the inverse can be computed *explicitly in terms of `S`*: the shift by `t • Iso n`
only produces

* a `Ric₀ ∧ id`-term with coefficient `chSg1 n b b' = (b - b')/(1 + (n-2)b')`, and
* an `Iso`-term with coefficient `chSg2 n a a' t (scalAlg S) = (t + 2·scalAlg S·(a-a')/n)/(1+2(n-1)a')`.

Concretely (this is the `t`-general form of the identity documented in
`Submission/Work/Diff/Alg/Pinch/ChatShiftDefs.lean`, where it is named `linv_ell_add_smul_Iso`):

`linv a' b' (ell a b S + t • Iso n) = S + chSg1 n b b' • (Ric₀ S ∧ id) + chSg2 n a a' t (scalAlg S) • Iso n`.

It is used to push the "shift inclusion" `X + Iso n ∈ Ĉ(s+δ)` (for `X ∈ Ĉ(s)`) into the
`Dpic`-picture: with `(a,b,p)` resp. `(a',b',p')` the Brendle–Schoen parameters of `Ĉ(s)` and
`Ĉ(s+δ)`, and `X = ell a b S`, the shifted tensor has `linv a' b' (X + Iso n) = S + γ₁·(Ric₀ S ∧ id) + γ₂·Iso n`.

The proof uses only linearity of `linv` (`linv_add`, `linv_smul`), the computation
`linv a' b' (Iso n) = (1+2(n-1)a')⁻¹ • Iso n` (`cm_linv_iso`), the identities
`ric0 (ell a b S) = (1+(n-2)b) • ric0 S` (`ric0_ell_linv`), `scalAlg (ell a b S) = (1+2(n-1)a)·scalAlg S`
(`scalAlg_ell_of_ne`) and `knProd (id2 n) (id2 n) = 2 • Iso n` (`knProd_id2_id2`). -/
theorem linv_ell_add_smul_Iso (n : ℕ) (hn : ((n : ℝ)) ≠ 0) {a b a' b' t : ℝ}
    (ha' : 1 + 2 * ((n : ℝ) - 1) * a' ≠ 0) (hb' : 1 + ((n : ℝ) - 2) * b' ≠ 0)
    {S : Curv4 n} (hS : IsAlgCurv S) :
    linv a' b' (ell a b S + t • Iso n)
      = S + chSg1 n b b' • knProd (ric0 S) (id2 n) + chSg2 n a a' t (scalAlg S) • Iso n := by
  -- `Ric₀` and `scalAlg` of `ell a b S`
  have hric0ell : ric0 (ell a b S) = (1 + ((n : ℝ) - 2) * b) • ric0 S := by
    funext i j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ric0_ell_linv n a b hn hS i j
  have hscalell : scalAlg (ell a b S) = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S :=
    scalAlg_ell_of_ne n a b hn hS
  -- the same for the shifted tensor `ell a b S + t • Iso n`
  have hric0Y : ric0 (ell a b S + t • Iso n) = (1 + ((n : ℝ) - 2) * b) • ric0 S := by
    rw [ric0_add', ric0_smul', hric0ell, ric0_iso, smul_zero, add_zero]
  have hscalY : scalAlg (ell a b S + t • Iso n)
      = (1 + 2 * ((n : ℝ) - 1) * a) * scalAlg S + t * ((n : ℝ) * ((n : ℝ) - 1)) := by
    rw [scalAlg_add_linv, scalAlg_smul_linv, hscalell, scalAlg_iso]
  -- unfold `linv`, `ell` and `chSg1`, `chSg2`
  rw [linv, hric0Y, hscalY, knProd_smul_left_linv, ell, knProd_id2_id2, chSg1, chSg2]
  -- name the two denominators so that `field_simp` can discharge them by assumption
  set Bb : ℝ := 1 + ((n : ℝ) - 2) * b' with hBbd
  set A' : ℝ := 1 + 2 * ((n : ℝ) - 1) * a' with hA'd
  have hBbnz : Bb ≠ 0 := by rw [hBbd]; exact hb'
  have hA'nz : A' ≠ 0 := by rw [hA'd]; exact ha'
  funext i j k l
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  rw [hBbd, hA'd]
  ring

end Work.Diff.Alg.Pinch
