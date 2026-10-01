/-
# ZeroFreeTables — Tables.lean

Heath-Brown's tables, transcribed from the paper, together with the **certificate**
that the two lists `rows15`, `rows14` of `Submission.Work.ZeroFreeTables.Defs`
(the frozen statement of AREA 3) are exactly the paper's tables lowered by the
safety margin `0.001`, plus the routing data that says, for every row, *which*
entry of *which* table justifies it.  Everything in the certificate is a rational
computation and is proved by `decide`/`norm_num`.

Transcriptions (page numbers of the author's version of [HB]):

* `hbTable8` — Table 8, p. 54, "λ₀ in the complex case": 21 rows `(λ₁, λ₀)`.
  The printed entry at `λ₁ = 0.66` is `0.783`, a **typo** for `0.738`: the column
  of Table 8 is decreasing (`0.816, 0.789, 0.763, ·, 0.714, 0.696`), and `0.738`
  is what the paper's inequality (9.13) gives (it is certified with margin
  `5.1·10⁻⁴` in `Table8CertExtPrinted.lean`).  The corrected value `738/1000` is
  the one recorded below; the printed `0.783` is not a valid table entry for
  λ₁ = 0.66 (it exceeds the entry at λ₁ = 0.64).
* `hbTable9` — Table 9, p. 55, "λ_j in the complex case": 20 rows `(λ₁, λ_j)`.
* `hbTable10` — Table 10, p. 56, "λ₂ in the complex case": 20 rows `(λ₁, λ₂)`.
* `hbTable7` — Table 7, p. 47, "λ₂ for real χ₁ and ρ₁": 17 rows `(λ₁, λ₂)`.
* `hbTable4` — Table 4, p. 43, "λ₀ for real χ₁ and ρ₁": 24 rows `(λ₁, λ₀)`
  (read as: `λ₁ ≤ printed λ₁` implies the bound).
* `hbTable7phi3` — the recomputation of the four rows of Table 7 needed below,
  with `φ(χ₁) = 1/3` instead of HB's `1/4` (ROUTE_LEAD Appendix A, `table7f.py`,
  and ROUTE_LEAD §4.3).

All five transcriptions are lists of *pairs of rationals* so that the certificate
is a kernel computation.
-/
import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.API

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## HB's printed tables, as rational data -/

/-- HB Table 8 (p. 54), `λ₀` in the complex case: `(λ₁, λ₀)`. -/
def hbTable8 : List (ℚ × ℚ) :=
  [((30/100 : ℚ), (1526/1000 : ℚ)), ((32/100 : ℚ), (1446/1000 : ℚ)), ((34/100 : ℚ), (1374/1000 : ℚ)), ((36/100 : ℚ), (1309/1000 : ℚ)), ((38/100 : ℚ), (1250/1000 : ℚ)), ((40/100 : ℚ), (1196/1000 : ℚ)), ((42/100 : ℚ), (1145/1000 : ℚ)), ((44/100 : ℚ), (1099/1000 : ℚ)), ((46/100 : ℚ), (1055/1000 : ℚ)), ((48/100 : ℚ), (1015/1000 : ℚ)), ((50/100 : ℚ), (977/1000 : ℚ)), ((52/100 : ℚ), (941/1000 : ℚ)), ((54/100 : ℚ), (907/1000 : ℚ)), ((56/100 : ℚ), (875/1000 : ℚ)), ((58/100 : ℚ), (845/1000 : ℚ)), ((60/100 : ℚ), (816/1000 : ℚ)), ((62/100 : ℚ), (789/1000 : ℚ)), ((64/100 : ℚ), (763/1000 : ℚ)), ((66/100 : ℚ), (738/1000 : ℚ)), ((68/100 : ℚ), (714/1000 : ℚ)), ((696/1000 : ℚ), (696/1000 : ℚ))]

/-- HB Table 9 (p. 55), `λ_j` in the complex case: `(λ₁, λ_j)`. -/
def hbTable9 : List (ℚ × ℚ) :=
  [((34/100 : ℚ), (1283/1000 : ℚ)), ((36/100 : ℚ), (1230/1000 : ℚ)), ((38/100 : ℚ), (1181/1000 : ℚ)), ((40/100 : ℚ), (1135/1000 : ℚ)), ((42/100 : ℚ), (1094/1000 : ℚ)), ((44/100 : ℚ), (1055/1000 : ℚ)), ((46/100 : ℚ), (1018/1000 : ℚ)), ((48/100 : ℚ), (984/1000 : ℚ)), ((50/100 : ℚ), (952/1000 : ℚ)), ((52/100 : ℚ), (922/1000 : ℚ)), ((54/100 : ℚ), (893/1000 : ℚ)), ((56/100 : ℚ), (866/1000 : ℚ)), ((58/100 : ℚ), (840/1000 : ℚ)), ((60/100 : ℚ), (816/1000 : ℚ)), ((62/100 : ℚ), (792/1000 : ℚ)), ((64/100 : ℚ), (770/1000 : ℚ)), ((66/100 : ℚ), (748/1000 : ℚ)), ((68/100 : ℚ), (728/1000 : ℚ)), ((70/100 : ℚ), (708/1000 : ℚ)), ((704/1000 : ℚ), (704/1000 : ℚ))]

/-- HB Table 10 (p. 56), `λ₂` in the complex case: `(λ₁, λ₂)`. -/
def hbTable10 : List (ℚ × ℚ) :=
  [((34/100 : ℚ), (929/1000 : ℚ)), ((36/100 : ℚ), (903/1000 : ℚ)), ((38/100 : ℚ), (887/1000 : ℚ)), ((40/100 : ℚ), (871/1000 : ℚ)), ((42/100 : ℚ), (856/1000 : ℚ)), ((44/100 : ℚ), (842/1000 : ℚ)), ((46/100 : ℚ), (829/1000 : ℚ)), ((48/100 : ℚ), (816/1000 : ℚ)), ((50/100 : ℚ), (803/1000 : ℚ)), ((52/100 : ℚ), (791/1000 : ℚ)), ((54/100 : ℚ), (780/1000 : ℚ)), ((56/100 : ℚ), (769/1000 : ℚ)), ((58/100 : ℚ), (759/1000 : ℚ)), ((60/100 : ℚ), (749/1000 : ℚ)), ((62/100 : ℚ), (739/1000 : ℚ)), ((64/100 : ℚ), (730/1000 : ℚ)), ((66/100 : ℚ), (721/1000 : ℚ)), ((68/100 : ℚ), (712/1000 : ℚ)), ((70/100 : ℚ), (704/1000 : ℚ)), ((702/1000 : ℚ), (702/1000 : ℚ))]

/-- HB Table 7 (p. 47), `λ₂` for real `χ₁`, `ρ₁`: `(λ₁, λ₂)`. -/
def hbTable7 : List (ℚ × ℚ) :=
  [((10/100 : ℚ), (276/100 : ℚ)), ((12/100 : ℚ), (256/100 : ℚ)), ((14/100 : ℚ), (239/100 : ℚ)), ((16/100 : ℚ), (225/100 : ℚ)), ((18/100 : ℚ), (212/100 : ℚ)), ((20/100 : ℚ), (201/100 : ℚ)), ((25/100 : ℚ), (177/100 : ℚ)), ((30/100 : ℚ), (158/100 : ℚ)), ((35/100 : ℚ), (142/100 : ℚ)), ((40/100 : ℚ), (129/100 : ℚ)), ((45/100 : ℚ), (118/100 : ℚ)), ((50/100 : ℚ), (108/100 : ℚ)), ((55/100 : ℚ), (100/100 : ℚ)), ((60/100 : ℚ), (92/100 : ℚ)), ((65/100 : ℚ), (85/100 : ℚ)), ((70/100 : ℚ), (79/100 : ℚ)), ((745/1000 : ℚ), (745/1000 : ℚ))]

/-- HB Table 4 (p. 43), `λ₀` for real `χ₁`, `ρ₁`: `(λ₁, λ₀)`, meaning
`λ₁ ≤ printed λ₁ ⟹ λ₀ ≥ printed λ₀`. -/
def hbTable4 : List (ℚ × ℚ) :=
  [((30/100 : ℚ), (2293/1000 : ℚ)), ((35/100 : ℚ), (2195/1000 : ℚ)),
   ((40/100 : ℚ), (2108/1000 : ℚ)), ((45/100 : ℚ), (2030/1000 : ℚ)),
   ((50/100 : ℚ), (1958/1000 : ℚ)), ((55/100 : ℚ), (1893/1000 : ℚ)),
   ((60/100 : ℚ), (1832/1000 : ℚ)), ((65/100 : ℚ), (1776/1000 : ℚ)),
   ((70/100 : ℚ), (1724/1000 : ℚ)), ((75/100 : ℚ), (1676/1000 : ℚ)),
   ((80/100 : ℚ), (1630/1000 : ℚ)), ((85/100 : ℚ), (1587/1000 : ℚ)),
   ((90/100 : ℚ), (1547/1000 : ℚ)), ((95/100 : ℚ), (1509/1000 : ℚ)),
   ((100/100 : ℚ), (1473/1000 : ℚ)), ((105/100 : ℚ), (1439/1000 : ℚ)),
   ((110/100 : ℚ), (1406/1000 : ℚ)), ((115/100 : ℚ), (1375/1000 : ℚ)),
   ((1175/1000 : ℚ), (1360/1000 : ℚ)), ((120/100 : ℚ), (1346/1000 : ℚ)),
   ((1225/1000 : ℚ), (1331/1000 : ℚ)), ((1250/1000 : ℚ), (1318/1000 : ℚ)),
   ((1275/1000 : ℚ), (1304/1000 : ℚ)), ((1294/1000 : ℚ), (1294/1000 : ℚ))]

/-- HB Lemma 8.7 recomputed with `φ(χ₁) = 1/3` (ROUTE_LEAD §4.3): `(λ₁, λ₂)`. -/
def hbTable7phi3 : List (ℚ × ℚ) :=
  [((20/100 : ℚ), (1804/1000 : ℚ)), ((25/100 : ℚ), (1588/1000 : ℚ)),
   ((30/100 : ℚ), (1418/1000 : ℚ)), ((35/100 : ℚ), (1279/1000 : ℚ)),
   ((40/100 : ℚ), (1154/1000 : ℚ))]

/-! ## The rows of the frozen statement, over `ℚ` -/

/-- `rows15` of `Defs.lean`, as rationals (literally the same thirteen rows). -/
def rows15Q : List (ℚ × ℚ × ℚ × ℚ × ℚ) :=
  [((348/1000 : ℚ), (36/100 : ℚ), (1308/1000 : ℚ), (902/1000 : ℚ), (1229/1000 : ℚ)),
   ((36/100 : ℚ), (38/100 : ℚ), (1249/1000 : ℚ), (886/1000 : ℚ), (1180/1000 : ℚ)),
   ((38/100 : ℚ), (40/100 : ℚ), (1195/1000 : ℚ), (870/1000 : ℚ), (1134/1000 : ℚ)),
   ((40/100 : ℚ), (42/100 : ℚ), (1144/1000 : ℚ), (855/1000 : ℚ), (1093/1000 : ℚ)),
   ((42/100 : ℚ), (44/100 : ℚ), (1098/1000 : ℚ), (841/1000 : ℚ), (1054/1000 : ℚ)),
   ((44/100 : ℚ), (46/100 : ℚ), (1054/1000 : ℚ), (828/1000 : ℚ), (1017/1000 : ℚ)),
   ((46/100 : ℚ), (48/100 : ℚ), (1014/1000 : ℚ), (815/1000 : ℚ), (983/1000 : ℚ)),
   ((48/100 : ℚ), (50/100 : ℚ), (976/1000 : ℚ), (802/1000 : ℚ), (951/1000 : ℚ)),
   ((50/100 : ℚ), (52/100 : ℚ), (940/1000 : ℚ), (790/1000 : ℚ), (921/1000 : ℚ)),
   ((52/100 : ℚ), (54/100 : ℚ), (906/1000 : ℚ), (779/1000 : ℚ), (892/1000 : ℚ)),
   ((54/100 : ℚ), (56/100 : ℚ), (874/1000 : ℚ), (768/1000 : ℚ), (865/1000 : ℚ)),
   ((56/100 : ℚ), (58/100 : ℚ), (844/1000 : ℚ), (758/1000 : ℚ), (856/1000 : ℚ)),
   ((58/100 : ℚ), (60/100 : ℚ), (815/1000 : ℚ), (748/1000 : ℚ), (856/1000 : ℚ))]

/-- `rows14` of `Defs.lean`, as rationals. -/
def rows14Q : List (ℚ × ℚ × ℚ) :=
  [((3/10 : ℚ), (348/1000 : ℚ), (127/100 : ℚ)),
   ((25/100 : ℚ), (3/10 : ℚ), (141/100 : ℚ)),
   ((2/10 : ℚ), (25/100 : ℚ), (158/100 : ℚ)),
   ((0 : ℚ), (2/10 : ℚ), (18/10 : ℚ))]

/-- `rows15` is the coercion of `rows15Q`. -/
theorem rows15_eq : rows15 = rows15Q.map (fun r =>
    ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2.1 : ℝ), (r.2.2.2.1 : ℝ), (r.2.2.2.2 : ℝ))) := by
  norm_num [rows15, rows15Q, Work.LinnikContract.rows15]

/-- `rows14` is the coercion of `rows14Q`. -/
theorem rows14_eq : rows14 = rows14Q.map (fun r => ((r.1 : ℝ), (r.2.1 : ℝ), (r.2.2 : ℝ))) := by
  norm_num [rows14, rows14Q, Work.LinnikContract.rows14]

theorem rows15Q_length : rows15Q.length = 13 := rfl

theorem rows14Q_length : rows14Q.length = 4 := rfl

/-! ## Provenance: the rows are the paper's tables lowered by `0.001` -/

/-- The thirteen entries of HB Table 8 selected by `rows15` (at the right end of
each interval). -/
def t8sel : List (ℚ × ℚ) :=
  [((36/100 : ℚ), (1309/1000 : ℚ)), ((38/100 : ℚ), (1250/1000 : ℚ)),
   ((40/100 : ℚ), (1196/1000 : ℚ)), ((42/100 : ℚ), (1145/1000 : ℚ)),
   ((44/100 : ℚ), (1099/1000 : ℚ)), ((46/100 : ℚ), (1055/1000 : ℚ)),
   ((48/100 : ℚ), (1015/1000 : ℚ)), ((50/100 : ℚ), (977/1000 : ℚ)),
   ((52/100 : ℚ), (941/1000 : ℚ)), ((54/100 : ℚ), (907/1000 : ℚ)),
   ((56/100 : ℚ), (875/1000 : ℚ)), ((58/100 : ℚ), (845/1000 : ℚ)),
   ((60/100 : ℚ), (816/1000 : ℚ))]

/-- The thirteen entries of HB Table 9 selected by `rows15`. -/
def t9sel : List (ℚ × ℚ) :=
  [((36/100 : ℚ), (1230/1000 : ℚ)), ((38/100 : ℚ), (1181/1000 : ℚ)),
   ((40/100 : ℚ), (1135/1000 : ℚ)), ((42/100 : ℚ), (1094/1000 : ℚ)),
   ((44/100 : ℚ), (1055/1000 : ℚ)), ((46/100 : ℚ), (1018/1000 : ℚ)),
   ((48/100 : ℚ), (984/1000 : ℚ)), ((50/100 : ℚ), (952/1000 : ℚ)),
   ((52/100 : ℚ), (922/1000 : ℚ)), ((54/100 : ℚ), (893/1000 : ℚ)),
   ((56/100 : ℚ), (866/1000 : ℚ)), ((58/100 : ℚ), (840/1000 : ℚ)),
   ((60/100 : ℚ), (816/1000 : ℚ))]

/-- The thirteen entries of HB Table 10 selected by `rows15`. -/
def t10sel : List (ℚ × ℚ) :=
  [((36/100 : ℚ), (903/1000 : ℚ)), ((38/100 : ℚ), (887/1000 : ℚ)),
   ((40/100 : ℚ), (871/1000 : ℚ)), ((42/100 : ℚ), (856/1000 : ℚ)),
   ((44/100 : ℚ), (842/1000 : ℚ)), ((46/100 : ℚ), (829/1000 : ℚ)),
   ((48/100 : ℚ), (816/1000 : ℚ)), ((50/100 : ℚ), (803/1000 : ℚ)),
   ((52/100 : ℚ), (791/1000 : ℚ)), ((54/100 : ℚ), (780/1000 : ℚ)),
   ((56/100 : ℚ), (769/1000 : ℚ)), ((58/100 : ℚ), (759/1000 : ℚ)),
   ((60/100 : ℚ), (749/1000 : ℚ))]

/-- Every selected entry really occurs in the transcription of the printed table. -/
theorem t8sel_mem : ∀ p ∈ t8sel, p ∈ hbTable8 := by
  intro p hp
  simp only [t8sel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; simp [hbTable8]

theorem t9sel_mem : ∀ p ∈ t9sel, p ∈ hbTable9 := by
  intro p hp
  simp only [t9sel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; simp [hbTable9]

theorem t10sel_mem : ∀ p ∈ t10sel, p ∈ hbTable10 := by
  intro p hp
  simp only [t10sel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; simp [hbTable10]

/-- The `λ₀` column of `rows15` is HB Table 8, read at the right end of each
interval and lowered by `1/1000`. -/
theorem rows15_lam0_prov :
    rows15Q.map (fun r => (r.2.1, r.2.2.1)) = t8sel.map (fun p => (p.1, p.2 - 1/1000)) := by
  simp only [rows15Q, t8sel, List.map_cons, List.map_nil]
  norm_num

/-- The `λ₂` column of `rows15` is HB Table 10, read at the right end of each
interval and lowered by `1/1000`. -/
theorem rows15_lam2_prov :
    rows15Q.map (fun r => (r.2.1, r.2.2.2.1)) = t10sel.map (fun p => (p.1, p.2 - 1/1000)) := by
  simp only [rows15Q, t10sel, List.map_cons, List.map_nil]
  norm_num

/-- The `λ₃` column of `rows15` is HB Table 9, read at the right end of each
interval, lowered by `1/1000` and capped by `107/125` (which is below
`6/7 - 1/1000`, so that Lemma 10.3 supplies it as well). -/
theorem rows15_lam3_prov :
    rows15Q.map (fun r => (r.2.1, r.2.2.2.2))
      = t9sel.map (fun p => (p.1, max (p.2 - 1/1000) (107/125))) := by
  simp only [rows15Q, t9sel, List.map_cons, List.map_nil]
  norm_num

/-- The cap `107/125` is below `6/7 - 1/1000`, so that a bound `λ₃ ≥ 107/125`
follows from HB Lemma 10.3 (`λ₃ ≥ 6/7`). -/
theorem cap_le_six_sevenths : (107/125 : ℚ) ≤ 6/7 - 1/1000 := by norm_num

/-! ## Routing: which table justifies which row

For every row of `rows15`, the `λ₀`/`λ₂`/`λ₃` entry is below an entry of the
corresponding printed table at an argument `≥` the right end of the row, so that
the paper's table statement for that entry gives the row's bound by monotonicity.
For `λ₃` the alternative route is the universal `λ₃ ≥ 6/7` of Lemma 10.3 (which
covers exactly the last two rows, where Table 9 is weaker).
For `rows14`, the bounds are below the `φ = 1/3` recomputation of Lemma 8.7 and
also below HB's printed Table 7. -/

/-- For every row of `rows15`, the `λ₀` entry is below an entry of HB Table 8 read at
an argument `≥` the right end of the row (so the paper's table statement gives the
row's bound by monotonicity). -/
theorem rows15_lam0_route : ∀ r ∈ rows15Q, ∃ p ∈ hbTable8, r.2.1 ≤ p.1 ∧ r.2.2.1 ≤ p.2 := by
  intro r hr
  have h1 : (r.2.1, r.2.2.1) ∈ rows15Q.map (fun r => (r.2.1, r.2.2.1)) :=
    List.mem_map.2 ⟨r, hr, rfl⟩
  rw [rows15_lam0_prov] at h1
  obtain ⟨p, hp, hp'⟩ := List.mem_map.mp h1
  have hp1 : p.1 = r.2.1 := by simpa using congrArg Prod.fst hp'
  have hp2 : r.2.2.1 ≤ p.2 := by
    have h := congrArg Prod.snd hp'
    simp only [Prod.mk.injEq] at h
    linarith
  exact ⟨p, t8sel_mem p hp, by rw [hp1], hp2⟩

/-- Same for the `λ₂` column and HB Table 10. -/
theorem rows15_lam2_route : ∀ r ∈ rows15Q, ∃ p ∈ hbTable10, r.2.1 ≤ p.1 ∧ r.2.2.2.1 ≤ p.2 := by
  intro r hr
  have h1 : (r.2.1, r.2.2.2.1) ∈ rows15Q.map (fun r => (r.2.1, r.2.2.2.1)) :=
    List.mem_map.2 ⟨r, hr, rfl⟩
  rw [rows15_lam2_prov] at h1
  obtain ⟨p, hp, hp'⟩ := List.mem_map.mp h1
  have hp1 : p.1 = r.2.1 := by simpa using congrArg Prod.fst hp'
  have hp2 : r.2.2.2.1 ≤ p.2 := by
    have h := congrArg Prod.snd hp'
    simp only [Prod.mk.injEq] at h
    linarith
  exact ⟨p, t10sel_mem p hp, by rw [hp1], hp2⟩

/-- Same for the `λ₃` column and HB Table 9, with the alternative route `λ₃ ≤ 6/7`
(Lemma 10.3) for the last two rows. -/
theorem rows15_lam3_route : ∀ r ∈ rows15Q,
    r.2.2.2.2 ≤ 107/125 ∨ ∃ p ∈ hbTable9, r.2.1 ≤ p.1 ∧ r.2.2.2.2 ≤ p.2 := by
  intro r hr
  have h1 : (r.2.1, r.2.2.2.2) ∈ rows15Q.map (fun r => (r.2.1, r.2.2.2.2)) :=
    List.mem_map.2 ⟨r, hr, rfl⟩
  rw [rows15_lam3_prov] at h1
  obtain ⟨p, hp, hp'⟩ := List.mem_map.mp h1
  have hp1 : p.1 = r.2.1 := by simpa using congrArg Prod.fst hp'
  have hp2 : r.2.2.2.2 = max (p.2 - 1/1000) (107/125) := by
    have h := congrArg Prod.snd hp'
    simpa only [Prod.mk.injEq] using h.symm
  by_cases h : r.2.2.2.2 ≤ 107/125
  · exact Or.inl h
  · have h' : ¬ (max (p.2 - 1/1000) (107/125)) ≤ 107/125 := by rwa [← hp2]
    have hmax : 107/125 < max (p.2 - 1/1000) (107/125) := lt_of_not_ge h'
    have hlt : 107/125 < p.2 - 1/1000 := (lt_max_iff.mp hmax).resolve_right (lt_irrefl _)
    refine Or.inr ⟨p, t9sel_mem p hp, by rw [hp1], ?_⟩
    rw [hp2]
    exact max_le (by linarith) (by linarith [hlt])

/-- `rows14`'s bounds are below HB's printed Table 7. -/
theorem rows14_c_le_table7 : ∀ r ∈ rows14Q, ∃ p ∈ hbTable7, r.2.1 ≤ p.1 ∧ r.2.2 ≤ p.2 := by
  intro r hr
  simp only [rows14Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h
  · subst h; exact ⟨((35/100 : ℚ), (142/100 : ℚ)), by norm_num [hbTable7], by norm_num⟩
  · subst h; exact ⟨((30/100 : ℚ), (158/100 : ℚ)), by norm_num [hbTable7], by norm_num⟩
  · subst h; exact ⟨((25/100 : ℚ), (177/100 : ℚ)), by norm_num [hbTable7], by norm_num⟩
  · subst h; exact ⟨((20/100 : ℚ), (201/100 : ℚ)), by norm_num [hbTable7], by norm_num⟩

/-- `rows14`'s bounds are below the `φ = 1/3` recomputation of Lemma 8.7. -/
theorem rows14_c_le_table7phi3 : ∀ r ∈ rows14Q,
    ∃ p ∈ hbTable7phi3, r.2.1 ≤ p.1 ∧ r.2.2 ≤ p.2 := by
  intro r hr
  simp only [rows14Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h
  · subst h; exact ⟨((35/100 : ℚ), (1279/1000 : ℚ)), by norm_num [hbTable7phi3], by norm_num⟩
  · subst h; exact ⟨((30/100 : ℚ), (1418/1000 : ℚ)), by norm_num [hbTable7phi3], by norm_num⟩
  · subst h; exact ⟨((25/100 : ℚ), (1588/1000 : ℚ)), by norm_num [hbTable7phi3], by norm_num⟩
  · subst h; exact ⟨((20/100 : ℚ), (1804/1000 : ℚ)), by norm_num [hbTable7phi3], by norm_num⟩

/-! ## Elementary shape of the tables -/

theorem rows15_lo_lt_hi : ∀ r ∈ rows15Q, r.1 < r.2.1 := by
  intro r hr
  simp only [rows15Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; norm_num

theorem rows14_lo_lt_hi : ∀ r ∈ rows14Q, r.1 < r.2.1 := by
  intro r hr
  simp only [rows14Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> · subst h; norm_num

/-- Every universal bound of `Z3` is dominated by every row of `rows15`:
the tables are consistent with HB Theorems 2 and Lemma 10.3. -/
theorem rows15_dominates_Z3 : ∀ r ∈ rows15Q,
    695/1000 ≤ r.2.2.1 ∧ 701/1000 ≤ r.2.2.2.1 ∧ 856/1000 ≤ r.2.2.2.2 := by
  intro r hr
  simp only [rows15Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; norm_num

theorem rows14_dominates_Z3 : ∀ r ∈ rows14Q, 695/1000 ≤ r.2.2 ∧ 701/1000 ≤ r.2.2 := by
  intro r hr
  simp only [rows14Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> · subst h; norm_num

/-- Every `λ₀` entry of `rows15` is below the universal real-case bound
`λ₀ ≥ 1.294` (HB Lemma 8.4), hence below `1.724 = 1724/1000` of Table 4. -/
theorem rows15_lam0_le_1724 : ∀ r ∈ rows15Q, r.2.2.1 ≤ 1724/1000 := by
  intro r hr
  simp only [rows15Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    · subst h; norm_num

theorem rows14_c_le_1800 : ∀ r ∈ rows14Q, r.2.2 ≤ 18/10 := by
  intro r hr
  simp only [rows14Q, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h <;> · subst h; norm_num

end Work.ZeroFreeTables
