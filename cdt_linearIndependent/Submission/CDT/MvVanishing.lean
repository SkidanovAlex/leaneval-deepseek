import Mathlib
import Submission.Commons.RingTheory.MvPowerSeries.exists_finset_sum_eq

open MvPowerSeries
open scoped BigOperators

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-
# The multivariate vanishing filtration (start of the paper's §"Filtered evaluation modules")

The paper's Lemma `total jumps` and Corollary `jumps Cartesian` concern the *vanishing filtration* of
a finite-dimensional subspace `V ⊆ ℚ⟦x₁,…,x_d⟧`: the filtration of `ℚ⟦x⟧` by the total order `≺` of
the exponents (total degree first, then lexicographic), whose steps are

`F^{(n)} = span{ x^m : n ≼ m }`,

and the *vanishing filtration jumps* `V_{D,Ω}^I` = the exponents that occur as the `≺`-minimal
exponent of a nonzero element of `V`.  The two facts are

* (`total jumps`) `#𝒱 = rank`, i.e. `#{leadExp f : f ∈ V, f ≠ 0} = finrank K V`;
* (`commutation` / `jumps Cartesian`) `𝒱(V ⊗ W) = 𝒱(V) × 𝒱(W)` for the Cartesian product.

The univariate case `#𝒱 = finrank` is `Commons.RingTheory.PowerSeries.ncard_vanishingOrders_eq_finrank`.

**This module** contains the definitions and the basic API of the multivariate theory:

* `tdeg s = |s| = Σ_i s_i` — the total degree of an exponent vector;
* `dk s = (|s|, s)` — the degree-lex *key* of an exponent, with the lexicographic order on pairs
  (`Lex (ℕ × Lex (σ →₀ ℕ))`), i.e. the paper's total order `≺`;
* `degLevel N` — the (finite) set of exponent vectors of total degree `N`
  (finiteness from `Commons.RingTheory.MvPowerSeries.exists_finset_sum_eq`);
* `minDeg f` — the minimal total degree of a nonzero multivariate power series;
* **`leadExp f`** — the `≺`-minimal exponent of the support of `f` (the "leading exponent"), with
  `coeff_leadExp_ne_zero`, `tdeg_leadExp` (`|leadExp f| = minDeg f`), `leadExp_le` and
  `leadExp_le_of_coeff_ne_zero` (`s ⪰ leadExp f` for every exponent `s` of the support) and
  `mem_lexStep_of_le_leadExp`;
* the two filtrations: `degStep V N` (all monomials of degree `≥ N`) with
  `mem_degStep_iff_minDeg`, `degStep_antitone`, and `lexStep V n` (all monomials `≻`-larger than the
  key `n`) with `lexStep_antitone`, `dk_udk_leadExp`, `mem_lexStep_of_le_leadExp`, and the
  compatibility
  **`lexStep_le_degStep`** (a `lexStep` of a key of total degree `N` sits inside `degStep V N`).

**The remaining steps** (next session) towards `#𝒱 = finrank`:

1. `degStep V N = ⊥` for `N ≫ 0` (the degree filtration of a finite-dimensional subspace is
   separated; same argument as the univariate `exists_vanishStep_eq_bot`);
2. for each `N`, with `J_N` the set of leading exponents of total degree `N`, the chain
   `lexStep V n₁ ⊋ lexStep V n₂ ⊋ … ⊋ lexStep V n_k ⊋ degStep V (N+1)`
   (`n₁ < … < n_k` the increasing enumeration of `J_N`, strict because the element realizing `n_i`
   lies in `lexStep V n_i` — all its monomials are `⪰` its leading exponent — but not in the next
   step); telescoping `Module.finrank` gives `#J_N ≤ finrank (degStep V N) − finrank (degStep V (N+1))`;
3. telescoping over `N` gives `#𝒱 = Σ_N #J_N = Σ_N (drops) = finrank V`;
4. `jumps Cartesian`: the two inclusions, the first by the product construction
   `leadExp (f·g) = (leadExp f, leadExp g)` (using `|leadExp| = minDeg` and `s ⪰ leadExp`), the
   second by specialisation/coefficient extraction `ℚ⟦x,y⟧ → ℚ⟦x⟧` (which maps an element of the
   product space with leading exponent `(n₁,n₂)` to an element of `V` with leading exponent `n₁`).
-/

namespace Submission.CDT.MvVanishing

variable {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]

/-- The total degree `|n| = n_1 + … + n_d` of an exponent vector. -/
def tdeg (s : σ →₀ ℕ) : ℕ := ∑ i, s i

/-- The degree-lex *key* `(|n|, n)` of an exponent vector, with the lexicographic order on pairs:
this is the total order `≺` of the paper's vanishing filtration (total degree first, then
lexicographic in the exponents). -/
def dk (s : σ →₀ ℕ) : Lex (ℕ × Lex (σ →₀ ℕ)) := toLex (tdeg s, toLex s)

/-- The exponent vector underlying a degree-lex key. -/
def udk (n : Lex (ℕ × Lex (σ →₀ ℕ))) : σ →₀ ℕ := ofLex (ofLex n).2

@[simp] theorem udk_dk (s : σ →₀ ℕ) : udk (dk s) = s := rfl

theorem dk_injective : Function.Injective (dk (σ := σ)) := fun s t h => by
  have := congrArg udk h
  simpa using this

theorem dk_lt_iff (s t : σ →₀ ℕ) :
    dk s < dk t ↔ tdeg s < tdeg t ∨ (tdeg s = tdeg t ∧ toLex s < toLex t) :=
  Prod.Lex.toLex_lt_toLex

theorem dk_lt_of_tdeg_lt {s t : σ →₀ ℕ} (h : tdeg s < tdeg t) : dk s < dk t :=
  (dk_lt_iff s t).mpr (Or.inl h)

theorem dk_lt_of_tdeg_lt_fst {s : σ →₀ ℕ} {n : Lex (ℕ × Lex (σ →₀ ℕ))}
    (h : tdeg s < (ofLex n).1) : dk s < n := by
  rw [dk]
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem dk_le_iff (s t : σ →₀ ℕ) :
    dk s ≤ dk t ↔ tdeg s < tdeg t ∨ (tdeg s = tdeg t ∧ toLex s ≤ toLex t) :=
  Prod.Lex.toLex_le_toLex

/-- The exponent vectors of total degree `N`. -/
noncomputable def degLevel (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Classical.choose (Commons.RingTheory.MvPowerSeries.exists_finset_sum_eq (σ := σ) N)).filter
    (fun s => tdeg s = N)

theorem mem_degLevel_iff {N : ℕ} {s : σ →₀ ℕ} : s ∈ degLevel N ↔ tdeg s = N := by
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Classical.choose_spec (Commons.RingTheory.MvPowerSeries.exists_finset_sum_eq (σ := σ) N)
        s h, h⟩

theorem exists_tdeg_coeff_ne_zero (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    ∃ N : ℕ, ∃ s : σ →₀ ℕ, tdeg s = N ∧ (coeff s) f ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (MvPowerSeries.ext fun s => h (tdeg s) s rfl)

/-- The minimal total degree of a nonzero multivariate power series. -/
noncomputable def minDeg (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) : ℕ :=
  Nat.find (exists_tdeg_coeff_ne_zero f hf)

theorem minDeg_spec (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    ∃ s : σ →₀ ℕ, tdeg s = minDeg f hf ∧ (coeff s) f ≠ 0 :=
  Nat.find_spec (exists_tdeg_coeff_ne_zero f hf)

theorem minDeg_le (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) {s : σ →₀ ℕ} (hs : (coeff s) f ≠ 0) :
    minDeg f hf ≤ tdeg s := Nat.find_min' (exists_tdeg_coeff_ne_zero f hf) ⟨s, rfl, hs⟩

theorem mem_degLevel_minDeg (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) {s : σ →₀ ℕ}
    (hs : (coeff s) f ≠ 0) (hdeg : tdeg s = minDeg f hf) : s ∈ degLevel (minDeg f hf) :=
  mem_degLevel_iff.mpr hdeg

/-- The degree-lex keys of the monomials of `f` of minimal total degree. -/
noncomputable def leadLevel (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    Finset (Lex (ℕ × Lex (σ →₀ ℕ))) :=
  ((degLevel (minDeg f hf)).filter (fun s => (coeff s) f ≠ 0)).image dk

theorem leadLevel_nonempty (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    (leadLevel f hf).Nonempty := by
  obtain ⟨s, hs1, hs2⟩ := minDeg_spec f hf
  exact ⟨dk s, Finset.mem_image.mpr
    ⟨s, Finset.mem_filter.mpr ⟨mem_degLevel_iff.mpr hs1, hs2⟩, rfl⟩⟩

/-- The degree-lex leading exponent `≺` of a nonzero multivariate power series: the minimal
exponent of its support for the order `≺` (total degree first, then lexicographic). -/
noncomputable def leadExp (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) : Lex (ℕ × Lex (σ →₀ ℕ)) :=
  Finset.min' (leadLevel f hf) (leadLevel_nonempty f hf)

theorem leadExp_mem (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    udk (leadExp f hf) ∈ (degLevel (minDeg f hf)).filter (fun s => (coeff s) f ≠ 0) := by
  obtain ⟨s, hs, hseq⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (leadLevel f hf) (leadLevel_nonempty f hf))
  have hmin : leadExp f hf = dk s := hseq.symm
  rw [hmin, udk_dk]
  exact hs

theorem coeff_leadExp_ne_zero (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    (coeff (udk (leadExp f hf))) f ≠ 0 :=
  (Finset.mem_filter.mp (leadExp_mem f hf)).2

theorem tdeg_leadExp (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    tdeg (udk (leadExp f hf)) = minDeg f hf :=
  mem_degLevel_iff.mp (Finset.mem_filter.mp (leadExp_mem f hf)).1

theorem leadExp_le (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) {s : σ →₀ ℕ}
    (hs : (coeff s) f ≠ 0) (hdeg : tdeg s = minDeg f hf) :
    leadExp f hf ≤ dk s :=
  Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨s, Finset.mem_filter.mpr ⟨mem_degLevel_iff.mpr hdeg, hs⟩, rfl⟩)

/-- The key of the underlying exponent of `leadExp f` is `leadExp f` itself. -/
theorem dk_udk_leadExp (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) :
    dk (udk (leadExp f hf)) = leadExp f hf := by
  obtain ⟨s, _, hseq⟩ :=
    Finset.mem_image.mp (Finset.min'_mem (leadLevel f hf) (leadLevel_nonempty f hf))
  have hmin : leadExp f hf = dk s := hseq.symm
  rw [hmin, udk_dk]

/-- For every exponent `s` of the support of `f`, `s ⪰ leadExp f`. -/
theorem leadExp_le_of_coeff_ne_zero (f : MvPowerSeries σ ℝ) (hf : f ≠ 0) {s : σ →₀ ℕ}
    (hs : (coeff s) f ≠ 0) : leadExp f hf ≤ dk s := by
  rcases lt_or_ge (minDeg f hf) (tdeg s) with h | h
  · have h1 : tdeg (udk (leadExp f hf)) < tdeg s := by rw [tdeg_leadExp]; exact h
    exact (dk_udk_leadExp f hf).symm.le.trans (le_of_lt (dk_lt_of_tdeg_lt h1))
  · exact leadExp_le f hf hs (le_antisymm h (minDeg_le f hf hs))

/-- The `N`-th step of the degree filtration of `V`: the elements all of whose monomials have total
degree at least `N`. -/
def degStep (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) : Submodule ℝ (MvPowerSeries σ ℝ) where
  carrier := {f | f ∈ V ∧ ∀ s : σ →₀ ℕ, tdeg s < N → (coeff s) f = 0}
  zero_mem' := ⟨V.zero_mem, by intro s _; simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨V.add_mem ha1 hb1, fun s hs => by
      rw [map_add, ha2 s hs, hb2 s hs, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨V.smul_mem c ha1, fun s hs => by rw [map_smul, ha2 s hs, smul_zero]⟩

theorem mem_degStep {V : Submodule ℝ (MvPowerSeries σ ℝ)} {N : ℕ}
    {f : MvPowerSeries σ ℝ} :
    f ∈ degStep V N ↔ f ∈ V ∧ ∀ s : σ →₀ ℕ, tdeg s < N → (coeff s) f = 0 := Iff.rfl

theorem degStep_le (V : Submodule ℝ (MvPowerSeries σ ℝ)) (N : ℕ) : degStep V N ≤ V :=
  fun _ h => h.1

@[simp]
theorem degStep_zero (V : Submodule ℝ (MvPowerSeries σ ℝ)) : degStep V 0 = V := by
  ext f
  simp [mem_degStep]

theorem degStep_antitone (V : Submodule ℝ (MvPowerSeries σ ℝ)) : Antitone (degStep V) := by
  intro m n hmn f hf
  exact ⟨hf.1, fun s hs => hf.2 s (lt_of_lt_of_le hs hmn)⟩

/-- An element of `V` lies in the `N`-th step of the degree filtration iff its minimal degree is at
least `N`. -/
theorem mem_degStep_iff_minDeg (V : Submodule ℝ (MvPowerSeries σ ℝ)) {N : ℕ}
    {f : MvPowerSeries σ ℝ} (hf : f ∈ V) (hne : f ≠ 0) :
    f ∈ degStep V N ↔ N ≤ minDeg f hne := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    obtain ⟨s, hs1, hs2⟩ := minDeg_spec f hne
    exact hs2 ((mem_degStep.mp h).2 s (by rw [hs1]; exact hlt))
  · intro h
    refine mem_degStep.mpr ⟨hf, fun s hs => ?_⟩
    by_contra hc
    exact absurd (minDeg_le f hne hc) (by omega)

/-- The `n`-th step of the *filtration by degree-lex keys*: the elements of `V` whose monomials are
all `⪰`-larger than the key `n`.  This is the filtration whose jumps are the leading exponents of
the elements of `V`. -/
def lexStep (V : Submodule ℝ (MvPowerSeries σ ℝ)) (n : Lex (ℕ × Lex (σ →₀ ℕ))) :
    Submodule ℝ (MvPowerSeries σ ℝ) where
  carrier := {f | f ∈ V ∧ ∀ s : σ →₀ ℕ, dk s < n → (coeff s) f = 0}
  zero_mem' := ⟨V.zero_mem, by intro s _; simp⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨V.add_mem ha1 hb1, fun s hs => by
      rw [map_add, ha2 s hs, hb2 s hs, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2⟩
    exact ⟨V.smul_mem c ha1, fun s hs => by rw [map_smul, ha2 s hs, smul_zero]⟩

theorem mem_lexStep {V : Submodule ℝ (MvPowerSeries σ ℝ)} {n : Lex (ℕ × Lex (σ →₀ ℕ))}
    {f : MvPowerSeries σ ℝ} :
    f ∈ lexStep V n ↔ f ∈ V ∧ ∀ s : σ →₀ ℕ, dk s < n → (coeff s) f = 0 := Iff.rfl

theorem lexStep_le (V : Submodule ℝ (MvPowerSeries σ ℝ)) (n) : lexStep V n ≤ V :=
  fun _ h => h.1

theorem lexStep_antitone (V : Submodule ℝ (MvPowerSeries σ ℝ)) : Antitone (lexStep V) := by
  intro m n hmn f hf
  exact ⟨hf.1, fun s hs => hf.2 s (lt_of_lt_of_le hs hmn)⟩

/-- **Compatibility of the two filtrations**: the lex-step of a key of total degree `N` is contained
in the `N`-th step of the degree filtration. -/
theorem lexStep_le_degStep (V : Submodule ℝ (MvPowerSeries σ ℝ))
    {n : Lex (ℕ × Lex (σ →₀ ℕ))} {N : ℕ} (hn : (ofLex n).1 = N) : lexStep V n ≤ degStep V N := by
  intro f hf
  refine mem_degStep.mpr ⟨hf.1, fun s hs => hf.2 s ?_⟩
  exact dk_lt_of_tdeg_lt_fst (by rw [hn]; exact hs)

/-- If the key `n` is below the leading exponent of `f ∈ V`, then `f` lies in the `n`-th lex-step:
every monomial of `f` is `⪰`-larger than its leading exponent, hence larger than `n`. -/
theorem mem_lexStep_of_le_leadExp (V : Submodule ℝ (MvPowerSeries σ ℝ))
    {n : Lex (ℕ × Lex (σ →₀ ℕ))} {f : MvPowerSeries σ ℝ} (hf : f ∈ V) (hne : f ≠ 0)
    (h : n ≤ leadExp f hne) : f ∈ lexStep V n := by
  refine mem_lexStep.mpr ⟨hf, fun s hs => ?_⟩
  by_contra hc
  exact absurd (leadExp_le_of_coeff_ne_zero f hne hc) (not_le.mpr (lt_of_lt_of_le hs h))

end Submission.CDT.MvVanishing
