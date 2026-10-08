import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.s02_lemma22Sq
import Submission.Work.BG.centralValue

/-!
# Area BG: `ViProp` (Bender–Glauberman 1981, the `(vi)`-core of Theorem 2.3)

`Work.BG.ViProp C` is the §2 core used in clause (vi) of the Coherence Theorem 2.3
(p. 206): if `μ, ν ∈ Irr(H₀)` lie in the same `Λ`-orbit with `μ^s ≠ μ`, `ν^s ≠ ν` and
`μ(t) = -ν(t)`, and if `(μ - ν)^G = g_μ - g_ν` with `g_μ, g_ν ∈ ±Irr(G)`, then
`g_ν(t) = 2 ν(t)`.

The proof is a three-line calculation from the inputs already in the workspace:

* **I-3** (`Work.BG.BSValueProp`, proved as `s02_bsValueAtT`):
  `(μ - ν)^G(t) = 2(μ(t) - ν(t)) = -4ν(t)`;
* **L2.2-d** (`Work.BG.Lemma22SqProp`, proved as `s02_lemma22Sq`):
  `g_μ(t)² = g_ν(t)²`;
* **L2.1-a** (`Work.BG.CentralValueProp`, proved as `centralValue`): `ν(t) ≠ 0`.

Since `g_μ(t) - g_ν(t) = (μ - ν)^G(t) = -4ν(t) ≠ 0`, the factorisation
`g_μ(t)² - g_ν(t)² = (g_μ(t) - g_ν(t))(g_μ(t) + g_ν(t)) = 0` gives `g_μ(t) = -g_ν(t)`,
and then `-2g_ν(t) = -4ν(t)`, i.e. `g_ν(t) = 2ν(t)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG in
theorem l41Vi {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] : Work.BG.ViProp C := by
  intro μ ν hμ hν hlam hμs hνs ht gμ gν hgμ hgν hAB
  -- I-3: the value of the induced difference at `t`.
  have hBS : ind C (μ - ν) (C.t : G) = 2 * (μ C.t - ν C.t) :=
    s02_bsValueAtT C μ ν hμ hν hlam
  -- The hypothesis `(μ - ν)^G = g_μ - g_ν`, evaluated at `t`.
  have hpt : ind C (μ - ν) (C.t : G) = gμ (C.t : G) - gν (C.t : G) := by
    have h := congrArg (fun φ : ClassFunction G ℂ => φ (C.t : G)) hAB
    simpa only [ClassFunction.sub_apply] using h
  -- Hence `g_μ(t) - g_ν(t) = 2(μ(t) - ν(t)) = -4ν(t)`.
  have h1 : gμ (C.t : G) - gν (C.t : G) = -4 * ν C.t := by
    rw [← hpt, hBS, ht]
    ring
  -- L2.2-d: `g_μ(t)² = g_ν(t)²`.
  have h2 : gμ (C.t : G) ^ 2 = gν (C.t : G) ^ 2 :=
    s02_lemma22Sq C μ ν hμ hν hlam hμs hνs gμ gν hgμ hgν hAB
  -- L2.1-a (Schur for the central involution `t`): `ν(t) = ±ν(1) ≠ 0`.
  have hc : ν C.t ≠ 0 := by
    obtain ⟨h, h1'⟩ := centralValue C ν hν
    rcases h with h | h
    · rw [h]; exact h1'
    · rw [h]; exact neg_ne_zero.mpr h1'
  have hne : gμ (C.t : G) - gν (C.t : G) ≠ 0 := by
    rw [h1]
    exact mul_ne_zero (by norm_num : (-4 : ℂ) ≠ 0) hc
  -- `(g_μ(t) - g_ν(t))(g_μ(t) + g_ν(t)) = g_μ(t)² - g_ν(t)² = 0`, so `g_μ(t) + g_ν(t) = 0`.
  have hb : gμ (C.t : G) + gν (C.t : G) = 0 := by
    have hprod : (gμ (C.t : G) - gν (C.t : G)) * (gμ (C.t : G) + gν (C.t : G)) = 0 := by
      have h : (gμ (C.t : G) + gν (C.t : G)) * (gμ (C.t : G) - gν (C.t : G)) = 0 := by
        rw [← sq_sub_sq]
        exact sub_eq_zero.mpr h2
      rwa [mul_comm (gμ (C.t : G) + gν (C.t : G)) (gμ (C.t : G) - gν (C.t : G))] at h
    exact (mul_eq_zero.mp hprod).resolve_left hne
  -- Combine: `-2g_ν(t) = -4ν(t)`, so `g_ν(t) = 2ν(t)`.
  have hkey : 2 * gν (C.t : G) = 4 * ν C.t := by
    linear_combination (-1 : ℂ) * h1 + (1 : ℂ) * hb
  linear_combination (1 / 2 : ℂ) * hkey

end Work.BG
