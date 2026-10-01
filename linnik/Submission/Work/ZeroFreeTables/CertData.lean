/-
# ZeroFreeTables — CertData.lean

The witness data of the two rational certificates of AREA 3, and the
von Mangoldt sum of HB §5.

* `t8certRows` — HB Table 8 (`λ₀` in the complex case) together with an explicit
  admissible value of HB's parameter `a` in Lemma 9.1 / (9.13):
  for every row `(lo, hi, v, a)`, with `K = Kaff hi`, the side condition
  `K₀(a+λ₁)⁻³ + (a+v)⁻³ ≥ a⁻³` holds and the left hand side of (9.13) is `≤ -0.0003`
  at `λ₁ = hi` (so it is `< 0` for every `λ₁ ≤ hi`, by monotonicity in `λ₁`).
  These witnesses were found by exact rational arithmetic; see
  `Submission/Work/ZeroFreeTables/dev/t8e.py` in the author's scratch directory.
* `p1014` — HB (10.14) specialised to `a = 3λ₃ = 18/7` (Lemma 10.3).
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.Engine

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-- HB Table 8 with an explicit witness `a` for HB Lemma 9.1, **targeting the
`λ₀`-column of the frozen `rows15`** (i.e. the printed entries lowered by `1/1000`):
`(lo, hi, v, a)` means "for `λ₁ ≤ hi`, taking `K = Kaff hi` and this `a`, the
paper's inequality (9.13) forces `λ₀ ≥ v`".  The witnesses were found by exact
rational search (`dev/t8h.py`); all margins are strictly negative (the tightest is
about `5·10⁻⁶` at `λ₁ ≤ 0.42`).

The polynomial used is HB's `P₃(X) = X + X² + (2/3)X³` of (4.12) — with the
coefficient `2/3`, not `1`: only this choice satisfies HB's condition (4.11). -/
def t8certRows : List (ℝ × ℝ × ℝ × ℝ) :=
  [((348/1000 : ℝ), (36/100 : ℝ), (1308/1000 : ℝ), (9/4 : ℝ)),
   ((36/100 : ℝ), (38/100 : ℝ), (1249/1000 : ℝ), (23/10 : ℝ)),
   ((38/100 : ℝ), (40/100 : ℝ), (1195/1000 : ℝ), (117/50 : ℝ)),
   ((40/100 : ℝ), (42/100 : ℝ), (1144/1000 : ℝ), (47/20 : ℝ)),
   ((42/100 : ℝ), (44/100 : ℝ), (1098/1000 : ℝ), (12/5 : ℝ)),
   ((44/100 : ℝ), (46/100 : ℝ), (1054/1000 : ℝ), (241/100 : ℝ)),
   ((46/100 : ℝ), (48/100 : ℝ), (1014/1000 : ℝ), (49/20 : ℝ)),
   ((48/100 : ℝ), (50/100 : ℝ), (976/1000 : ℝ), (247/100 : ℝ)),
   ((50/100 : ℝ), (52/100 : ℝ), (940/1000 : ℝ), (249/100 : ℝ)),
   ((52/100 : ℝ), (54/100 : ℝ), (906/1000 : ℝ), (5/2 : ℝ)),
   ((54/100 : ℝ), (56/100 : ℝ), (874/1000 : ℝ), (63/25 : ℝ)),
   ((56/100 : ℝ), (58/100 : ℝ), (844/1000 : ℝ), (127/50 : ℝ)),
   ((58/100 : ℝ), (60/100 : ℝ), (815/1000 : ℝ), (51/20 : ℝ))]

/-- The eight *remaining* printed entries of HB Table 8 (λ₁ = 0.30, 0.32, 0.34, 0.62,
0.64, 0.66, 0.68, 0.695), with explicit witnesses `a` and targets equal to the
printed values lowered by `1/1000` (for the last row the printed `0.696` is replaced by
`0.695`, since at `0.696` the inequality (9.13) is only tangent); together with `t8certRows` this certifies the
table completely.  (At λ₁ = 0.66 the printed entry `0.783` is a typo for `0.738` —
the column reads `0.816, 0.789, 0.763, 0.783, 0.714, 0.696`.) -/
def t8certRowsExt : List (ℝ × ℝ × ℝ × ℝ) :=
  [((30/100 : ℝ), (30/100 : ℝ), (1525/1000 : ℝ), (53/25 : ℝ)),
   ((32/100 : ℝ), (32/100 : ℝ), (1445/1000 : ℝ), (217/100 : ℝ)),
   ((34/100 : ℝ), (34/100 : ℝ), (1373/1000 : ℝ), (221/100 : ℝ)),
   ((62/100 : ℝ), (62/100 : ℝ), (788/1000 : ℝ), (257/100 : ℝ)),
   ((64/100 : ℝ), (64/100 : ℝ), (762/1000 : ℝ), (259/100 : ℝ)),
   ((66/100 : ℝ), (66/100 : ℝ), (737/1000 : ℝ), (259/100 : ℝ)),
   ((68/100 : ℝ), (68/100 : ℝ), (713/1000 : ℝ), (13/5 : ℝ)),
   ((695/1000 : ℝ), (695/1000 : ℝ), (695/1000 : ℝ), (129/50 : ℝ))]

/-- **HB Table 8, printed values, first thirteen entries.**  Same shape and meaning
as `t8certRows`, but the target `v` is now the entry *as printed in the paper*
(not lowered by `1/1000`): `(lo, hi, printed λ₀, a)`.  The witnesses were found by
exact rational arithmetic (`dev/t8h.py`, refined to a `1/1000` grid in `a`); the
tightest margin is about `7.5·10⁻⁵` (at `λ₁ ≤ 0.40`).  Consequently the whole
`0.001` safety margin built into the frozen `rows15` is *not needed* for Table 8,
and HB's printed table is certified as printed. -/
def t8certRowsP : List (ℝ × ℝ × ℝ × ℝ) :=
  [((348/1000 : ℝ), (36/100 : ℝ), (1309/1000 : ℝ), (1161/500 : ℝ)),
   ((36/100 : ℝ), (38/100 : ℝ), (1250/1000 : ℝ), (59/25 : ℝ)),
   ((38/100 : ℝ), (40/100 : ℝ), (1196/1000 : ℝ), (599/250 : ℝ)),
   ((40/100 : ℝ), (42/100 : ℝ), (1145/1000 : ℝ), (607/250 : ℝ)),
   ((42/100 : ℝ), (44/100 : ℝ), (1099/1000 : ℝ), (1229/500 : ℝ)),
   ((44/100 : ℝ), (46/100 : ℝ), (1055/1000 : ℝ), (1243/500 : ℝ)),
   ((46/100 : ℝ), (48/100 : ℝ), (1015/1000 : ℝ), (2511/1000 : ℝ)),
   ((48/100 : ℝ), (50/100 : ℝ), (977/1000 : ℝ), (507/200 : ℝ)),
   ((50/100 : ℝ), (52/100 : ℝ), (941/1000 : ℝ), (639/250 : ℝ)),
   ((52/100 : ℝ), (54/100 : ℝ), (907/1000 : ℝ), (322/125 : ℝ)),
   ((54/100 : ℝ), (56/100 : ℝ), (875/1000 : ℝ), (519/200 : ℝ)),
   ((56/100 : ℝ), (58/100 : ℝ), (845/1000 : ℝ), (653/250 : ℝ)),
   ((58/100 : ℝ), (60/100 : ℝ), (816/1000 : ℝ), (657/250 : ℝ))]

/-- **HB Table 8, printed values, the remaining eight entries** (`λ₁ = 0.30, 0.32,
0.34, 0.62, 0.64, 0.66, 0.68, 0.696`).  The entry printed at `λ₁ = 0.66` reads
`0.783`, a typo for `0.738` (the column is `0.816, 0.789, 0.763, 0.783, 0.714,
0.696`); the corrected value `0.738` is used, and it certifies with margin
`5.1·10⁻⁴`.  The last entry `(0.696, 0.696)` is *not* only tangent: with a better
witness `a` than the coarse search of `dev/t8h.py` it certifies with margin
`6.5·10⁻⁴`. -/
def t8certRowsExtP : List (ℝ × ℝ × ℝ × ℝ) :=
  [((30/100 : ℝ), (30/100 : ℝ), (1526/1000 : ℝ), (2181/1000 : ℝ)),
   ((32/100 : ℝ), (32/100 : ℝ), (1446/1000 : ℝ), (279/125 : ℝ)),
   ((34/100 : ℝ), (34/100 : ℝ), (1374/1000 : ℝ), (2279/1000 : ℝ)),
   ((62/100 : ℝ), (62/100 : ℝ), (789/1000 : ℝ), (2643/1000 : ℝ)),
   ((64/100 : ℝ), (64/100 : ℝ), (763/1000 : ℝ), (2657/1000 : ℝ)),
   ((66/100 : ℝ), (66/100 : ℝ), (738/1000 : ℝ), (267/100 : ℝ)),
   ((68/100 : ℝ), (68/100 : ℝ), (714/1000 : ℝ), (2681/1000 : ℝ)),
   ((696/1000 : ℝ), (696/1000 : ℝ), (696/1000 : ℝ), (269/100 : ℝ))]

/-- The von Mangoldt sum `K(s,χ) = Σ_n Λ(n) Re(χ(n)/n^s) f(log n / L)` of HB §5. -/
def Ksum (q : ℕ) [NeZero q] (f : ℝ → ℝ) (L : ℝ) (s : ℂ) (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) *
    ((χ (n : ZMod q) / (n : ℂ) ^ s).re) * f (Real.log n / L)

end Work.ZeroFreeTables
