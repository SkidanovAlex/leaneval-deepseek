import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.ChenPlan.LinearSieve.JR2.linear_sieve_upper_v6
import Submission.Work.ChenPlan.LinearSieve.JR2.linear_sieve_lower_v6
import Submission.Work.ChenPlan.LinearSieve.JR2.layer_sharp
import Submission.Work.ChenPlan.LinearSieve.JR2.selberg_sharp_low
import Submission.Work.ChenPlan.LinearSieve.JR2.riUp_riPsi_lipschitz

/-! Guidance from the project lead (the requester):

You own the linear sieve for Chen's theorem. Read `Submission/ChenPlan/Interfaces.lean` (v6) and
`Submission/Work/ChenPlan/LinearSieve/RIMain/ROUTE_STATUS_2026-09-24.md` (the previous owner's final report) FIRST.

HISTORY. The previous owner (H5) declared `linear_sieve` "wrong" under the v5 contract. It built a density family satisfying the
PRODUCT-form axioms (`IsLinear`, `IsLinearRange`, `IsLinearLower`) with per-layer excesses Θ(K). Two points: (a) its numerics stop
at z ≤ 1e5, where the classical error term O((log D)^{-1/3}) is still ≈ 0.35, so they do NOT refute the sharp theorem; (b) its
per-layer route with error O(K/log D) is genuinely false. The v6 contract settles it anyway: `IsLinearMertens` is Richert's
two-sided condition Ω₁ + Ω₂(1, L): ν ≤ 1/2 and |Σ_{w≤p<z'} ν(p) log p − log(z'/w)| ≤ K on every sub-range. H5's family violates
it (its weighted sum drifts like K·log log z'). This is exactly the hypothesis set of the JURKAT–RICHERT THEOREM.

ROUTE: Halberstam–Richert, *Sieve Methods*, Ch. 7 (Selberg's upper bound, whose sharp G-bound needs the two-sided Ω₂(1,L), now
available), Ch. 2 (fundamental lemma), and Ch. 8 (Jurkat–Richert: the functional inequalities S ≤ XV(F + error),
S ≥ XV(f − error) from Selberg + Buchstab iteration, with F(s) = 2e^γ/s on [1,3] (Utab is 1.005·2e^γ/s there) and
f(s) ≥ 0.9965 at s = 4.9, needing ≥ 993/1000). The error terms may decay as slowly as you like in D: the contract only asks
for ∃ D₀ z₀, and D₀ may be astronomically large. Do NOT aim for errors O(K/log D) per layer (refuted).
Reuse the proved bank (all sorry-free, listed in ROUTE_STATUS §4): `SelbergBound.selberg_bound`, `Selberg.gsum_bound_dense`,
`Selberg.selberg_pair.upperValidAll_selbergU` (already gives the upper half for s ≤ 2), `FundamentalLemma.fundamental_lemma_range`,
the Buchstab/child/Abel machinery, and the RI profile family (riUp, riPsi, profC, errH), which gives the F/f numerics.
Utab = F + 0.5% slack and 993/1000 = f(4.9) − 0.35%: keep the numerics honest (Numerics/ has riUp_le_Utab, riPsi_le).
Put new files under `Submission/Work/ChenPlan/LinearSieve/` (e.g. `JR/`). Delegate aggressively.
-/

namespace Work.ChenPlan.LinearSieve

/-- The linear (dimension-1) sieve, upper and lower forms, against the v6 contract (Richert's condition `IsLinearMertens`);
see `Submission/ChenPlan/Interfaces.lean`. -/
theorem linear_sieve_v6 : Submission.ChenPlan.LinearSieveUpper ∧ Submission.ChenPlan.LinearSieveLower :=
  ⟨JR2.linear_sieve_upper_v6 JR2.layer_sharp JR2.selberg_sharp_low JR2.riUp_riPsi_lipschitz,
   JR2.linear_sieve_lower_v6 JR2.layer_sharp JR2.riUp_riPsi_lipschitz⟩

end Work.ChenPlan.LinearSieve
