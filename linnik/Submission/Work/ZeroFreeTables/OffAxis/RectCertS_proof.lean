/-
# ZeroFreeTables/OffAxis — `RectCertS_proof`

**HB Theorems 2 and 3 at rectangle height `L`** (`Work.ZeroFreeTables.RectCertS`,
`OFFAXIS_ROUTE_LEAD.md` §3.1).

`RectCertS` asks, uniformly in `L ≥ 1` and `q ≥ q₀(L)`, for the three height-`L` bounds
`Lam0BoundH L χ₁ ρ₁ (695/1000)`, `Lam2BoundH L χ₁ (701/1000)`, `Lam3BoundH L χ₁ (856/1000)`
for every pair carrying the height-`L` numbering `IsRectStrip L χ₁ ρ₁` (minimality of `λ₁` over
the rectangle `|Im| ≤ L` plus HB Lemma 6.1's zero-free strip `(L, 10L]`).

These are exactly Heath-Brown's Theorems 2 and 3 (PLMS 64 (1992), p. 4) with the working
region `|t| ≤ 1` replaced by the rectangle `|t| ≤ L` of his §6 numbering `(6.1)`; the
constants are the paper's `0.696`, `0.702` and `6/7` lowered by `0.001` (the `λ₃` value is
additionally capped at `6/7`).  The three bounds are the three conjuncts of the certificate
and are established separately, each by Heath-Brown's §§6–10 engine run at rectangle height
`L`:

* `RectLam0` — the height-`L` `λ₀`-bound (Table 8 in the complex case via Lemma 9.1, Table 4
  in the real case via Lemmas 8.2/8.3, and the repeated-zero case via the `Rep9` core);
* `RectLam2` — the height-`L` `λ₂`-bound (Lemma 9.4 = Table 10 in all cases, `λ₂ ≥ 0.702`);
* `RectLam3` — the height-`L` `λ₃`-bound (Lemma 10.3, `λ₃ ≥ 6/7 − 1/1000`).

At `L = 1` the hypothesis `IsRectStrip 1` is the on-axis numbering and the three bounds are
the `Z3` statement of `Work.ZeroFreeTables.ZeroFreeCert`, so nothing is stated twice.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.HBTable4_proof
import Submission.Work.ZeroFreeTables.HBLemma9_4_proof
import Submission.Work.ZeroFreeTables.HBLemma9_1_proof
import Submission.Work.ZeroFreeTables.OffAxis.RectLam0
import Submission.Work.ZeroFreeTables.OffAxis.RectLam2
import Submission.Work.ZeroFreeTables.OffAxis.RectLam3

open DirichletCharacter

namespace Work.ZeroFreeTables.OffAxis

/-- **HB Theorems 2 and 3 at rectangle height `L`.**  The three conjuncts are the three
height-`L` bounds, supplied by `RectLam0`, `RectLam2` and `RectLam3`. -/
theorem RectCertS_proof : Work.ZeroFreeTables.RectCertS := by
  intro L hL
  obtain ⟨q0, h0⟩ := RectLam0 L hL
  obtain ⟨q2, h2⟩ := RectLam2 L hL
  obtain ⟨q3, h3⟩ := RectLam3 L hL
  refine ⟨max (max q0 q2) q3, ?_⟩
  intro q hq _ χ₁ ρ₁ hR
  have hq0 : q0 ≤ q := by omega
  have hq2 : q2 ≤ q := by omega
  have hq3 : q3 ≤ q := by omega
  exact ⟨h0 q hq0 χ₁ ρ₁ hR, h2 q hq2 χ₁ ρ₁ hR, h3 q hq3 χ₁ ρ₁ hR⟩

end Work.ZeroFreeTables.OffAxis
