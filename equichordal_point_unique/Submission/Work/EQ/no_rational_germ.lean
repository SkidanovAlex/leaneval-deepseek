import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germ_poly_identity
import Submission.Work.EQ.germ_no_other_roots
import Submission.Work.EQ.germ_setup
import Submission.Work.EQ.germ_reduce
import Submission.Work.EQ.germ_N_eq
import Submission.Work.EQ.germ_END
import Submission.Work.EQ.eq_endgame

/-! Guidance from the project lead: Rychlik Thm 12, second half.

**No rational stable germ.** For `0 < a < 1` the stable germ is not a rational function.

Route (see `DESIGN.md` §4 and the helper modules):

* `germ_setup` / `germ_reduce`: `h = N/D` near `0` with `D 0 ≠ 0`; `N` has a simple zero at `0`;
  reduce to a fraction `N'/D'` with no common root.
* `germ_poly_identity`: the squared germ equation, cleared of denominators, is the polynomial
  identity `(N₁D - ND₁)² (N₂D - ND₂)² = a² N² (N² + D²) (N₂D₁ - N₁D₂)²`.
* `germ_no_other_roots` (Rychlik's semi-projective/dynamical argument): `N'` has no root
  other than `0`.
* `germ_N_eq`: therefore `N' = c X` and `D'(0) = -c`.
* `germ_END` + `eq_endgame`: substituting into the polynomial identity yields, by a degree and
  coefficient comparison, the contradiction `λ = 1` (i.e. `a = 0`).
-/

namespace Work.EQ

open Filter Topology

/-- **No rational stable germ (Rychlik Thm 12, second half).** For `0 < a < 1` the stable germ
is not a rational function. -/
theorem no_rational_germ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ¬ ∃ N D : Polynomial ℂ, D.eval 0 ≠ 0 ∧ ∀ᶠ u in 𝓝 (0 : ℂ), h u * D.eval u = N.eval u := by
  rintro ⟨N, D, hD0, hDN⟩
  obtain ⟨hN, hN0, hNd⟩ := germ_setup ha0 ha1 hh hD0 hDN
  obtain ⟨N', D', hD'0, hDN', hnoCommon, hN'⟩ := germ_reduce hN hD0 hDN
  obtain ⟨c, hc, hN'eq, hD'0val⟩ :=
    germ_N_eq ha0 ha1 hh hD'0 hDN' hN'
      (fun z hz => germ_no_other_roots ha0 ha1 hh hD'0 hDN' hnoCommon hz)
  exact eq_endgame ha0 ha1 hc hD'0 (germ_END ha0 ha1 hh hD'0 hDN' hc hN'eq)

end Work.EQ
