import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.CDcl.rowdefs

/-!
# `Work.ADcl.yode14_defs`: the row data for the 14-tuple `fourteen a b c`

This is the `Fin 14` analogue of `Submission.Work.CDcl.rowdefs` (which is hard-wired to the
17-tuple `seventeen`): the slot embedding `eIdx14` of the seven `B`-functions into `fourteen`,
the `B`-row `rowB14`, the integral row `rowT14`, and the coefficient matrix `A14` of
`Work.ADcl.dclosed_of_yode`, with the common denominator `QF q0 q = X^4 * q0 * q`.

Indices of `Submission.CDTPlan.fourteen a b c`:

`0..4` = `B₁..B₅`, `5..8` = `G, G', G'', G'''`, `9,10` = `B₆, B₇`,
`11` = `∫G`, `12` = `∫(G − jet₁ G)/y`, `13` = `∫(G − jet₂ G)/y²`.
-/

namespace Work.ADcl

open PowerSeries Polynomial

noncomputable section

/-- The slot embedding of the seven `B`-functions into the 14-tuple: `0..4 ↦ 0..4`, `5 ↦ 9`,
`6 ↦ 10`. -/
def eIdx14 (a : Fin 7) : Fin 14 :=
  if h : a.val < 5 then ⟨a.val, by omega⟩ else if a.val = 5 then 9 else 10

lemma eIdx14_inj : Function.Injective eIdx14 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [eIdx14] at h ⊢

/-- `fourteen` restricts to `pureB` along the slot embedding `eIdx14`. -/
lemma fourteen_eIdx14 (a b c : ℤ) (i : Fin 7) :
    Submission.CDTPlan.fourteen a b c (eIdx14 i) = Submission.CDTPlan.pureB i := by
  fin_cases i <;> simp [eIdx14, Submission.CDTPlan.fourteen, Submission.CDTPlan.pureB]

/-- The common denominator `X^4 * q₀ * q` of `Work.ADcl.dclosed_of_yode`. -/
def QF (q0 q : Polynomial ℚ) : Polynomial ℚ := Polynomial.X ^ 4 * q0 * q

lemma QF_ne_zero {q0 q : Polynomial ℚ} (h0 : q0 ≠ 0) (h : q ≠ 0) : QF q0 q ≠ 0 := by
  rw [QF]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 4 Polynomial.X_ne_zero) h0) h

/-- The row of the seven `B`-functions of the 14-tuple: `X^4 * A0 a k` in the `k`-th `B`-slot,
`0` elsewhere. -/
def rowB14 (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7)
    (j : Fin 14) : Polynomial ℚ :=
  if j.val = 0 then Polynomial.X ^ 4 * A0 a 0
  else if j.val = 1 then Polynomial.X ^ 4 * A0 a 1
  else if j.val = 2 then Polynomial.X ^ 4 * A0 a 2
  else if j.val = 3 then Polynomial.X ^ 4 * A0 a 3
  else if j.val = 4 then Polynomial.X ^ 4 * A0 a 4
  else if j.val = 9 then Polynomial.X ^ 4 * A0 a 5
  else if j.val = 10 then Polynomial.X ^ 4 * A0 a 6
  else 0

/-- The row of `∫ (G − jet_k G)/y^k` for `k = 1,2` in the 14-tuple: `X^{4-k} q₀ q` on `G` and
`−X^{4-k} q₀ q · jet_k G` on `B₁ = 1`. -/
def rowT14 (q0 q : Polynomial ℚ) (G : PowerSeries ℚ) (k : ℕ) (j : Fin 14) : Polynomial ℚ :=
  if j.val = 5 then Polynomial.X ^ (4 - k) * q0 * q
  else if j.val = 0 then -(Polynomial.X ^ (4 - k) * q0 * q * Work.CDcl.jet k G)
  else 0

/-- The coefficient matrix of `Work.ADcl.dclosed_of_yode`.  Column `j` indexes
`Submission.CDTPlan.fourteen a b c j`.

* rows `0..4, 9, 10` (`B₁..B₅, B₆, B₇`): `q * rowB14 q0 A0 i`, i.e. `X^4 q₀ q · A0 i k` in the
  `k`-th `B`-slot;
* rows `5,6,7` (`G, G', G''`): `QF q0 q` in the next column;
* row `8` (`G'''`): `X^4 q₀ · A k` on column `5+k` (`k < 4`) and `X^4 q₀ · cc` on column `0`
  (the inhomogeneity `cc · B₁`);
* row `11` (`∫G`): `QF q0 q` on column `5` (`G`);
* rows `12,13` (`∫ (G − jet_k G)/y^k`, `k = 1,2`): `rowT14 q0 q G k`. -/
def A14 (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (A : Fin 4 → Polynomial ℚ)
    (cc : Polynomial ℚ) (G : PowerSeries ℚ) (i j : Fin 14) : Polynomial ℚ :=
  if _ : i.val < 5 then q * rowB14 q0 A0 ⟨i.val, by omega⟩ j
  else if i.val = 5 then (if j.val = 6 then QF q0 q else 0)
  else if i.val = 6 then (if j.val = 7 then QF q0 q else 0)
  else if i.val = 7 then (if j.val = 8 then QF q0 q else 0)
  else if i.val = 8 then
    (if j.val = 5 then Polynomial.X ^ 4 * q0 * A 0
     else if j.val = 6 then Polynomial.X ^ 4 * q0 * A 1
     else if j.val = 7 then Polynomial.X ^ 4 * q0 * A 2
     else if j.val = 8 then Polynomial.X ^ 4 * q0 * A 3
     else if j.val = 0 then Polynomial.X ^ 4 * q0 * cc
     else 0)
  else if i.val = 9 then q * rowB14 q0 A0 5 j
  else if i.val = 10 then q * rowB14 q0 A0 6 j
  else if i.val = 11 then (if j.val = 5 then QF q0 q else 0)
  else if i.val = 12 then rowT14 q0 q G 1 j
  else if i.val = 13 then rowT14 q0 q G 2 j
  else 0

/-- On the `B`-slots, `A14` is `q` times the rescaled row `rowB14`. -/
lemma A14_Brow (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ) (G : PowerSeries ℚ) (a : Fin 7) (j : Fin 14) :
    A14 q0 q A0 A cc G (eIdx14 a) j = q * rowB14 q0 A0 a j := by
  fin_cases a <;> simp [A14, eIdx14]

/-- `rowB14` evaluated at a `B`-slot. -/
lemma rowB14_eIdx14 (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a b : Fin 7) :
    rowB14 q0 A0 a (eIdx14 b) = Polynomial.X ^ 4 * A0 a b := by
  fin_cases b <;> simp [rowB14, eIdx14]

/-- `rowB14` vanishes off the `B`-slots. -/
lemma rowB14_zero (q0 : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7)
    {j : Fin 14} (h : j ∉ Set.range eIdx14) : rowB14 q0 A0 a j = 0 := by
  have h5 : ¬ j.val < 5 := by
    intro hlt
    exact h ⟨⟨j.val, by omega⟩, by ext; simp [eIdx14, hlt]⟩
  have h9 : j.val ≠ 9 := by
    intro h9
    exact h ⟨5, by ext; simp [eIdx14, h9]⟩
  have h10 : j.val ≠ 10 := by
    intro h10
    exact h ⟨6, by ext; simp [eIdx14, h10]⟩
  have h0 : j.val ≠ 0 := by omega
  have h1 : j.val ≠ 1 := by omega
  have h2 : j.val ≠ 2 := by omega
  have h3 : j.val ≠ 3 := by omega
  have h4 : j.val ≠ 4 := by omega
  simp [rowB14, h0, h1, h2, h3, h4, h9, h10]

/-- A sum over `Fin 14` whose summand vanishes off the slots `eIdx14` collapses to a sum over
`Fin 7`. -/
lemma sum_eIdx14 {M : Type*} [AddCommMonoid M] (f : Fin 14 → M)
    (h : ∀ j, j ∉ Set.range eIdx14 → f j = 0) :
    ∑ j : Fin 14, f j = ∑ a : Fin 7, f (eIdx14 a) := by
  classical
  have hinj : Set.InjOn eIdx14 ↑(Finset.univ : Finset (Fin 7)) :=
    fun a _ b _ hab => eIdx14_inj hab
  have himg : (Finset.univ.filter (fun j : Fin 14 => j ∈ Set.range eIdx14))
      = Finset.image eIdx14 Finset.univ := by
    ext j; simp
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin 14)),
      x ∉ Finset.univ.filter (fun j : Fin 14 => j ∈ Set.range eIdx14) → f x = 0 := by
    intro x _ hx
    exact h x (by
      intro hmem
      exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hmem⟩))
  rw [← Finset.sum_subset
    (Finset.filter_subset (fun j : Fin 14 => j ∈ Set.range eIdx14) Finset.univ) hzero]
  rw [himg, Finset.sum_image hinj]

end

end Work.ADcl
