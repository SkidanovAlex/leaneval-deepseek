/-
  WilC4/CandBody_definable : `Work.WilC4.CandBody` is `univ`-definable in `LRc`.

  `CandBody Y B₀ ρ ⊆ ℝ^{CandIdx k}` is the quantifier-free "body" of the candidate formula: a
  Boolean combination of the conditions

    `0 < β`, `(x, u) ∈ Y`, `(z, v) ∈ Y`, `z = x · β`, `v = u · y`, `q₀ = x / β`,
    `¬(…)`, `(¬(…) ∨ …)`,

  where the last two blocks involve the breakpoint family `B₀`, the window variable `t`, and the
  real parameter `ρ`.

  Every atomic conjunct is one of

  * a `∅`-definable membership `g ∈ GrSub Y emb a b` / `g ∈ GrSub1 B₀ emb a`
    (`GrSub_definable`, `GrSub1_definable`);
  * the `∅`-definable order of `ℝ` (`real_definable_le`, `definable_eq_add`,
    `definable_lt_const`);
  * an `univ`-definable polynomial (in)equality with real coefficients
    (`definable_eval_eq_LRc`, `definable_le_LRc`, `definable_ne_LRc`), the coefficients being the
    constants `2`, `1` and the real parameter `ρ`;
  * the `univ`-definable division relation `IsDivR` (`definable_isDivR`, and its polynomial
    variant `definable_isDivR_poly` for the occurrences where a factor `2 · β` or the constant `1`
    plays the role of the denominator).

  The `∅`-pieces are upgraded to `univ`-definability with `Set.Definable.mono`; the outer
  `∧`, `∨`, `¬` are `Set.Definable.inter`/`union`/`compl`.  The parameter `ρ` enters only through
  the constants of `LRc`, so `univ`- and `∅`-definability agree here.
-/
import Mathlib
import Submission.Work.WilC4.DiagDefs

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc)

variable {k : ℕ}

namespace CandBodyDefs

/-! ## 1. Generic helpers -/

/-- `∅`-definability upgrades to `univ`-definability. -/
lemma univ_of_empty {α : Type*} {s : Set (α → ℝ)}
    (h : (∅ : Set ℝ).Definable LRc s) : (Set.univ : Set ℝ).Definable LRc s :=
  h.mono (Set.empty_subset _)

/-- `IsDivR` with numerator and denominator supplied by polynomials in the free variables, and
the quotient read off from a coordinate.  This is `definable_isDivR` with the numerator/denominator
replaced by arbitrary polynomial expressions, which is what the two occurrences
`IsDivR (g cx) (2 * g cβ) (g cq1)` and `IsDivR 1 (g cβ) (g cpinv)` need. -/
theorem definable_isDivR_poly {σ : Type*} (A B : MvPolynomial σ ℝ) (l : σ) :
    (Set.univ : Set ℝ).Definable LRc
      {u : σ → ℝ | IsDivR ((MvPolynomial.eval u) A) ((MvPolynomial.eval u) B) (u l)} := by
  have h1 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) B = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0}) :=
    (definable_eval_eq_LRc B 0).inter (definable_eval_eq_LRc (MvPolynomial.X l) 0)
  have h2 : (Set.univ : Set ℝ).Definable LRc
      ({u : σ → ℝ | (MvPolynomial.eval u) B ≠ 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l * B - A) = 0}) :=
    (definable_ne_LRc B 0).inter (definable_eval_eq_LRc (MvPolynomial.X l * B - A) 0)
  have h := h1.union h2
  have hset : ({u : σ → ℝ | (MvPolynomial.eval u) B = 0} ∩
        {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l) = 0} ∪
        ({u : σ → ℝ | (MvPolynomial.eval u) B ≠ 0} ∩
          {u : σ → ℝ | (MvPolynomial.eval u) (MvPolynomial.X l * B - A) = 0}))
      = {u : σ → ℝ | IsDivR ((MvPolynomial.eval u) A) ((MvPolynomial.eval u) B) (u l)} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, MvPolynomial.eval_X,
      MvPolynomial.eval_mul, MvPolynomial.eval_sub, IsDivR]
    constructor
    · rintro (⟨hb, hq⟩ | ⟨hb, hq⟩)
      · exact Or.inl ⟨hb, hq⟩
      · exact Or.inr ⟨hb, by linarith⟩
    · rintro (⟨hb, hq⟩ | ⟨hb, hq⟩)
      · exact Or.inl ⟨hb, hq⟩
      · exact Or.inr ⟨hb, by linarith⟩
  rw [hset] at h
  exact h

/-! ## 2. The nine pieces of `CandBody` -/

/-- `0 < β`. -/
def cbPos : Set (CandIdx k → ℝ) := {g | 0 < g cx}

/-- `(x, u) ∈ Y`, i.e. the value slot `cu` at the argument slot `cx` belongs to `Y`. -/
def cbYx (Y : Set (Fin (k+2) → ℝ)) : Set (CandIdx k → ℝ) := GrSub Y embC cx cu

/-- `(z, v) ∈ Y`, i.e. the value slot `cv` at the argument slot `cz` belongs to `Y`. -/
def cbYz (Y : Set (Fin (k+2) → ℝ)) : Set (CandIdx k → ℝ) := GrSub Y embC cz cv

/-- `z = x · β`. -/
def cbE4 : Set (CandIdx k → ℝ) := {g | g cz = g cx * g cβ}

/-- `v = u · y`. -/
def cbE5 : Set (CandIdx k → ℝ) := {g | g cv = g cu * g cy}

/-- `q₀ = x / β`. -/
def cbD6 : Set (CandIdx k → ℝ) := {g | IsDivR (g cx) (g cβ) (g cq0)}

/-- The body of the innermost `¬`: `b ∈ B₀`, `q₁ = x / (2β)`, `q₁ ≤ b ≤ 2β · x`. -/
def cbB7 (B₀ : Set (Fin (k+1) → ℝ)) : Set (CandIdx k → ℝ) :=
  Bmem B₀ ∩ {g | IsDivR (g cx) (2 * g cβ) (g cq1)} ∩ {g | g cq1 ≤ g cb} ∩
    {g | g cb ≤ 2 * g cβ * g cx}

/-- The body of the left disjunct of the window alternative: `q₀ ≤ t ≤ z`, `t₂ = 2t`,
`(t, y₁) ∈ Y`, `(t₂, y₂) ∈ Y` and `y₁ ≠ 0`. -/
def cbQ8 (Y : Set (Fin (k+2) → ℝ)) : Set (CandIdx k → ℝ) :=
  {g | g cq0 ≤ g ct} ∩ {g | g ct ≤ g cz} ∩ {g | g ct2 = g ct + g ct} ∩
    GrSub Y embC ct cy1 ∩ GrSub Y embC ct2 cy2 ∩ {g | g cy1 ≠ 0}

/-- The body of the right disjunct of the window alternative: `q = y₂ / y₁`,
`β⁻¹ = 1 / β` and `|q - β⁻¹| ≤ ρ`. -/
def cbR8 (ρ : ℝ) : Set (CandIdx k → ℝ) :=
  {g | IsDivR (g cy2) (g cy1) (g cqq)} ∩ {g | IsDivR 1 (g cβ) (g cpinv)} ∩
    {g | g cqq ≤ g cpinv + ρ} ∩ {g | ρ ≤ g cqq + g cpinv}

/-! ## 3. Definability of the pieces -/

lemma definable_cbPos : (Set.univ : Set ℝ).Definable LRc (cbPos (k := k)) :=
  univ_of_empty (definable_lt_const (ρ := CandIdx k) 0 cx)

lemma definable_cbYx {Y : Set (Fin (k+2) → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (cbYx (k := k) Y) :=
  univ_of_empty (GrSub_definable hY embC cx cu)

lemma definable_cbYz {Y : Set (Fin (k+2) → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (cbYz (k := k) Y) :=
  univ_of_empty (GrSub_definable hY embC cz cv)

lemma definable_cbE4 : (Set.univ : Set ℝ).Definable LRc (cbE4 (k := k)) := by
  have h := definable_eval_eq_LRc (σ := CandIdx k)
    (MvPolynomial.X cz - MvPolynomial.X cx * MvPolynomial.X cβ) 0
  convert h using 1
  ext g
  simp only [cbE4, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, sub_eq_zero]

lemma definable_cbE5 : (Set.univ : Set ℝ).Definable LRc (cbE5 (k := k)) := by
  have h := definable_eval_eq_LRc (σ := CandIdx k)
    (MvPolynomial.X cv - MvPolynomial.X cu * MvPolynomial.X cy) 0
  convert h using 1
  ext g
  simp only [cbE5, Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_mul,
    MvPolynomial.eval_X, sub_eq_zero]

lemma definable_cbD6 : (Set.univ : Set ℝ).Definable LRc (cbD6 (k := k)) :=
  definable_isDivR cx cβ cq0

lemma definable_cbB7 {B₀ : Set (Fin (k+1) → ℝ)} (hB₀ : (∅ : Set ℝ).Definable LRc B₀) :
    (Set.univ : Set ℝ).Definable LRc (cbB7 (k := k) B₀) := by
  have hB : (Set.univ : Set ℝ).Definable LRc (Bmem B₀) :=
    univ_of_empty (GrSub1_definable hB₀ cc cb)
  have hdiv : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | IsDivR (g cx) (2 * g cβ) (g cq1)} := by
    have h := definable_isDivR_poly (σ := CandIdx k)
      (MvPolynomial.X cx) (MvPolynomial.C 2 * MvPolynomial.X cβ) cq1
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_mul]
  have hle1 : (Set.univ : Set ℝ).Definable LRc {g : CandIdx k → ℝ | g cq1 ≤ g cb} :=
    univ_of_empty (real_definable_le cq1 cb)
  have hle2 : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | g cb ≤ 2 * g cβ * g cx} := by
    have h := definable_le_LRc (σ := CandIdx k)
      (MvPolynomial.X cb) (MvPolynomial.C 2 * MvPolynomial.X cβ * MvPolynomial.X cx)
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_mul]
  exact ((hB.inter hdiv).inter hle1).inter hle2

lemma definable_cbQ8 {Y : Set (Fin (k+2) → ℝ)} (hY : (∅ : Set ℝ).Definable LRc Y) :
    (Set.univ : Set ℝ).Definable LRc (cbQ8 (k := k) Y) := by
  have h1 : (Set.univ : Set ℝ).Definable LRc {g : CandIdx k → ℝ | g cq0 ≤ g ct} :=
    univ_of_empty (real_definable_le cq0 ct)
  have h2 : (Set.univ : Set ℝ).Definable LRc {g : CandIdx k → ℝ | g ct ≤ g cz} :=
    univ_of_empty (real_definable_le ct cz)
  have h3 : (Set.univ : Set ℝ).Definable LRc {g : CandIdx k → ℝ | g ct2 = g ct + g ct} :=
    univ_of_empty (definable_eq_add ct2 ct ct)
  have h4 : (Set.univ : Set ℝ).Definable LRc (GrSub Y embC ct cy1) :=
    univ_of_empty (GrSub_definable hY embC ct cy1)
  have h5 : (Set.univ : Set ℝ).Definable LRc (GrSub Y embC ct2 cy2) :=
    univ_of_empty (GrSub_definable hY embC ct2 cy2)
  have h6 : (Set.univ : Set ℝ).Definable LRc {g : CandIdx k → ℝ | g cy1 ≠ 0} := by
    have h := definable_ne_LRc (σ := CandIdx k) (MvPolynomial.X cy1) 0
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, map_zero]
  exact ((((h1.inter h2).inter h3).inter h4).inter h5).inter h6

lemma definable_cbR8 (ρ : ℝ) : (Set.univ : Set ℝ).Definable LRc (cbR8 (k := k) ρ) := by
  have h1 : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | IsDivR (g cy2) (g cy1) (g cqq)} :=
    definable_isDivR cy2 cy1 cqq
  have h2 : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | IsDivR 1 (g cβ) (g cpinv)} := by
    have h := definable_isDivR_poly (σ := CandIdx k)
      (MvPolynomial.C 1) (MvPolynomial.X cβ) cpinv
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C]
  have h3 : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | g cqq ≤ g cpinv + ρ} := by
    have h := definable_le_LRc (σ := CandIdx k)
      (MvPolynomial.X cqq) (MvPolynomial.X cpinv + MvPolynomial.C ρ)
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_add]
  have h4 : (Set.univ : Set ℝ).Definable LRc
      {g : CandIdx k → ℝ | ρ ≤ g cqq + g cpinv} := by
    have h := definable_le_LRc (σ := CandIdx k)
      (MvPolynomial.C ρ) (MvPolynomial.X cqq + MvPolynomial.X cpinv)
    convert h using 1
    ext g
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_C, MvPolynomial.eval_add]
  exact ((h1.inter h2).inter h3).inter h4

end CandBodyDefs

/-! ## 4. `CandBody` as a Boolean combination of the pieces -/

/-- `CandBody` is exactly the Boolean combination of the nine pieces `cbPos`, …, `cbR8`. -/
lemma CandBody_eq_pieces (Y : Set (Fin (k+2) → ℝ)) (B₀ : Set (Fin (k+1) → ℝ)) (ρ : ℝ) :
    CandBody Y B₀ ρ = CandBodyDefs.cbPos (k := k) ∩ CandBodyDefs.cbYx Y ∩
      CandBodyDefs.cbYz Y ∩ CandBodyDefs.cbE4 ∩ CandBodyDefs.cbE5 ∩ CandBodyDefs.cbD6 ∩
      (CandBodyDefs.cbB7 B₀)ᶜ ∩ ((CandBodyDefs.cbQ8 Y)ᶜ ∪ CandBodyDefs.cbR8 ρ) := by
  ext g
  simp only [CandBody, CandBodyDefs.cbPos, CandBodyDefs.cbYx, CandBodyDefs.cbYz,
    CandBodyDefs.cbE4, CandBodyDefs.cbE5, CandBodyDefs.cbD6, CandBodyDefs.cbB7,
    CandBodyDefs.cbQ8, CandBodyDefs.cbR8, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_union, Set.mem_compl_iff]
  tauto

theorem CandBody_definable {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (ρ : ℝ)
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀) :
    (Set.univ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.CandBody Y B₀ ρ) := by
  have h1 := CandBodyDefs.definable_cbPos (k := k)
  have h2 := CandBodyDefs.definable_cbYx (k := k) hY
  have h3 := CandBodyDefs.definable_cbYz (k := k) hY
  have h4 := CandBodyDefs.definable_cbE4 (k := k)
  have h5 := CandBodyDefs.definable_cbE5 (k := k)
  have h6 := CandBodyDefs.definable_cbD6 (k := k)
  have h7 := (CandBodyDefs.definable_cbB7 (k := k) hB₀).compl
  have h8 := (CandBodyDefs.definable_cbQ8 (k := k) hY).compl.union
    (CandBodyDefs.definable_cbR8 (k := k) ρ)
  rw [CandBody_eq_pieces Y B₀ ρ]
  exact (((((((h1.inter h2).inter h3).inter h4).inter h5).inter h6).inter h7).inter h8)

end Work.WilC4
