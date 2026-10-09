import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.witt.Vocab
import Submission.Work.SSGRoute.prop5.witt.leading_term_coeff
import Submission.Work.SSGRoute.prop5.witt.hall_spanning
import Submission.Work.SSGRoute.prop5.witt.hall_foliage_lt_right
import Submission.Work.SSGRoute.prop5.witt.Swap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN.md and the orchestrator's addendum DESIGN2 (copied as Submission/Work/SSGRoute/DESIGN2.md). Interfaces: Submission/Work/SSGRoute/Interfaces.lean (namespace SSGRoute; do NOT edit). NK.* CFT library available. Siblings in parallel.

# hallSpan_saturated  (Magnus/Witt purity, from Hall-basis unitriangularity)

**Statement.** The ℤ-span of `{monBrk h : h Hall, size h = j}` is saturated in `ℤ⟨X⟩`: if all
coefficients of `a` are divisible by `n ≠ 0`, then `a = n • b` with `b` in the span.

**Proof.** Everything needed is PROVED on disk:
- `witt.leading_term_coeff`: the coefficient of `monBrk h` at `foliage h` is `1`, and 0 at every smaller
  word;
- `witt.hall_foliage_injective`: distinct Hall trees have distinct foliages.

Write `a = Σ c_h monBrk h` (finite support; the Hall trees of size `j` over `supp a` are finitely many).
Suppose some `c_h` is not divisible by `n`, and take `h₀` of lex-minimal foliage among these.
- The coefficient of `a` at `foliage h₀` is `c_{h₀}` plus terms `c_h · coeff` over `h` with smaller
  foliage.
- Each such `c_h` is divisible by `n`, by minimality.
- Terms with larger foliage contribute 0.

So `n ∣ c_{h₀}`, a contradiction.

**Wiring hazard (important).** Two different declarations named `Work.SSGRoute.prop5.monBrk` exist:
`magnusCore.lean:55` and `witt/Vocab.lean:47` (the `witt/Defs` one was just removed). Any module importing
both fails with "already declared". `dimensionSubgroup_free → magnusCore` and the Hall stack (`Vocab`) meet
in `adjacent_pSeries_inter_lcs_le` as soon as purity is wired. Delete the magnusCore copy, import `Vocab`,
and keep a `monBrk_eq`-style lemma if the types differ (`FreeAssoc X` is an abbrev of the same
`MonoidAlgebra`). This statement uses the `Vocab` one (elaborated with `import …prop5.witt.Vocab`).

**Imports.** `prop5.witt.Vocab`, `prop5.witt.leading_term_coeff`, `prop5.witt.hall_foliage_injective`.
**Size.** Medium-small (the finite-support bookkeeping is most of it).

# Proof as formalised (and a deviation in imports)

The proof below is the triangular ("unitriangular family") argument, in the form of the general
lemma `hallSpan_pure_of_leading`: a family `b : ι → ℤ⟨X⟩` whose *leading words* `f i` are pairwise
distinct, with `coeffF (b i) (f i) = 1` and `coeffF (b i) w = 0` for `w < f i`, spans a pure
submodule.  (Note that no homogeneity hypothesis is needed: for `n • v = Σ_{i ∈ s} α i • b i` and
`i₀ ∈ s` minimal for `f`, every other term of `s` contributes `0` to the coefficient of `f i₀`, so
`α i₀ = n · coeffF v (f i₀)`.)  Saturation of the Hall span then follows by writing `a = n • m`
with `m := divCoeff X n a` the coordinatewise quotient of `a` by `n` (legitimate because
`n ∣ a.coeff w`), so that `n • m ∈ HallSpan ⟹ m ∈ HallSpan`, and `a = n • m`.

**Imports.** `prop5.magnusFramework` (for `FreeAssoc`), `prop5.witt.Vocab` (for `monBrk`,
`coeffF`), `prop5.witt.leading_term_coeff` (the leading-term theorem *with* its `swap` hypothesis,
supplied by `prop5.witt.hall_foliage_lt_right` and `prop5.witt.Swap`), and
`prop5.witt.hall_spanning` (for `hall_foliage_injective_aux`).  The originally suggested
`prop5.magnus_leadingTerm` (which contains a `sorry` and is not needed here) and the
`prop5.witt.monBrk_leading` route were dropped: `monBrk_leading` declares
`prop5.witt.SuppAbove`, which clashes with the mainstream `prop5.witt.leading_term_coeff`, and
using `prop5.witt.hall_spanning` instead of `prop5.witt.hall_foliage_injective` keeps
`prop5.witt.Defs` (hence its `IsLyndon`) out of this file's closure, so this module can be imported
together with both the `witt.Defs`-flavoured and the `magnusLieDefs`-flavoured parts of the tree.
-/

namespace Work.SSGRoute

open SSGRoute

/-! ## Auxiliary lemmas

The argument is the classical triangular ("unitriangular family") one; the Hall input is
`witt.leading_term_coeff` (the coefficient of `monBrk h` at the foliage word `foliage h` is `1`,
and `0` at every smaller word) together with `witt.hall_foliage_injective_aux` (a Hall tree is
determined by its foliage). -/

/-- The coefficient of a fixed word, as a `ℤ`-linear functional on the free associative algebra
`ℤ⟨X⟩ = FreeAssoc X`. -/
private def coeffLin (X : Type*) (w : FreeMonoid X) :
    Work.SSGRoute.prop5.FreeAssoc X →ₗ[ℤ] ℤ where
  toFun a := a.coeff w
  map_add' a b := by
    show MonoidAlgebra.coeff (a + b) w = MonoidAlgebra.coeff a w + MonoidAlgebra.coeff b w
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c a := by
    show MonoidAlgebra.coeff (c • a) w = c • MonoidAlgebra.coeff a w
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

private theorem coeffLin_ofList {X : Type*} (w : List X)
    (a : Work.SSGRoute.prop5.FreeAssoc X) :
    coeffLin X (FreeMonoid.ofList w) a = Work.SSGRoute.prop5.coeffF a w := rfl

/-- The "swap" inequality for the two foliage blocks of a Hall product. -/
private theorem foliage_swap {X : Type*} [LinearOrder X] {a b : Work.SSGRoute.prop5.Magma X}
    (hab : Work.SSGRoute.prop5.IsHall (Work.SSGRoute.prop5.Magma.mul a b)) :
    Work.SSGRoute.prop5.Magma.foliage a ++ Work.SSGRoute.prop5.Magma.foliage b
      < Work.SSGRoute.prop5.Magma.foliage b ++ Work.SSGRoute.prop5.Magma.foliage a :=
  Work.SSGRoute.prop5.swap_hall_of_crux
    (fun _ _ h => Work.SSGRoute.prop5.witt.hall_foliage_lt_right h) hab

private theorem monBrk_coeffF_lead {X : Type*} [LinearOrder X]
    {h : Work.SSGRoute.prop5.Magma X} (hh : Work.SSGRoute.prop5.IsHall h) :
    Work.SSGRoute.prop5.coeffF (Work.SSGRoute.prop5.monBrk X h)
        (Work.SSGRoute.prop5.Magma.foliage h) = 1 ∧
      ∀ w : List X, w < Work.SSGRoute.prop5.Magma.foliage h →
        Work.SSGRoute.prop5.coeffF (Work.SSGRoute.prop5.monBrk X h) w = 0 := by
  have hswap : ∀ a b : Work.SSGRoute.prop5.Magma X,
      Work.SSGRoute.prop5.IsHall (Work.SSGRoute.prop5.Magma.mul a b) →
      Work.SSGRoute.prop5.Magma.foliage a ++ Work.SSGRoute.prop5.Magma.foliage b
        < Work.SSGRoute.prop5.Magma.foliage b ++ Work.SSGRoute.prop5.Magma.foliage a :=
    fun _ _ hab => foliage_swap hab
  exact ⟨(Work.SSGRoute.prop5.witt.leading_term_coeff hh hswap).1,
    fun w hw => (Work.SSGRoute.prop5.witt.leading_term_coeff hh hswap).2 w hw⟩

/-- A `ℤ`-algebra element divisible by `n ≠ 0` vanishes. -/
private theorem eq_zero_of_smul_eq_zero {X : Type*} {n : ℤ} (hn : n ≠ 0)
    {u : Work.SSGRoute.prop5.FreeAssoc X} (h : n • u = 0) : u = 0 := by
  apply MonoidAlgebra.ext
  ext w
  have h1 : n * u.coeff w = 0 := by
    have h2 : (n • u).coeff w = 0 := by
      rw [h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rwa [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at h2
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact absurd h3 hn
  · rw [h3, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- **Purity of the span of a unitriangular family.**  Let `b : ι → ℤ⟨X⟩` be a family of elements
whose "leading words" `f i` are pairwise distinct, `b i` having coefficient `1` at `f i` and
coefficient `0` at every lexicographically smaller word.  Then the `ℤ`-span of the family is
saturated: for `n ≠ 0`, `n • v` in the span implies `v` in the span.

Proof: write `n • v = Σ_{i ∈ s} α i • b i`.  If `s ≠ ∅`, pick `i₀ ∈ s` with `f i₀` minimal.  For
`i ∈ s`, `i ≠ i₀` we have `f i₀ < f i`, so `b i` contributes `0` to the coefficient of `f i₀`;
hence the coefficient of `n • v` at `f i₀` is `α i₀`, i.e. `n ∣ α i₀`.  Removing the term
`i₀` and dividing by `n`, the number of terms drops, and induction on `s.card` concludes. -/
theorem hallSpan_pure_of_leading {X : Type*} [LinearOrder X] {ι : Type*}
    (f : ι → List X) (hf : Function.Injective f) (b : ι → Work.SSGRoute.prop5.FreeAssoc X)
    (hlead : ∀ i, Work.SSGRoute.prop5.coeffF (b i) (f i) = 1)
    (hbelow : ∀ i w, w < f i → Work.SSGRoute.prop5.coeffF (b i) w = 0)
    (n : ℤ) (hn : n ≠ 0) (v : Work.SSGRoute.prop5.FreeAssoc X)
    (h : n • v ∈ Submodule.span ℤ (Set.range b)) :
    v ∈ Submodule.span ℤ (Set.range b) := by
  classical
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := ℤ) (v := b)).mp h
  have key : ∀ (m : ℕ) (u : Work.SSGRoute.prop5.FreeAssoc X) (s : Finset ι) (α : ι → ℤ),
      s.card = m → (∑ i ∈ s, α i • b i) = n • u →
      u ∈ Submodule.span ℤ (Set.range b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u s α hcard hsum
      rcases s.eq_empty_or_nonempty with hem | hne
      · rw [hem, Finset.sum_empty] at hsum
        rw [eq_zero_of_smul_eq_zero hn hsum.symm]
        exact Submodule.zero_mem _
      · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image s f hne
        have hsingle : coeffLin X (FreeMonoid.ofList (f i₀)) (α i₀ • b i₀) = α i₀ := by
          rw [map_smul, smul_eq_mul, coeffLin_ofList, hlead i₀, mul_one]
        have hsum_coeff : coeffLin X (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
            = α i₀ := by
          rw [map_sum, ← hsingle]
          refine Finset.sum_eq_single i₀ ?_ ?_
          · intro i hi hne'
            have hlt : f i₀ < f i := lt_of_le_of_ne (hmin i hi) (fun hh => hne' (hf hh.symm))
            rw [map_smul, smul_eq_mul, coeffLin_ofList, hbelow i (f i₀) hlt, mul_zero]
          · intro h
            exact absurd hi₀ h
        have hcoeff : coeffLin X (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
            = coeffLin X (FreeMonoid.ofList (f i₀)) (n • u) := by rw [hsum]
        have hα : α i₀ = n * Work.SSGRoute.prop5.coeffF u (f i₀) := by
          rw [← hsum_coeff, hcoeff, map_smul, coeffLin_ofList, smul_eq_mul]
        have hstep : (∑ i ∈ s.erase i₀, α i • b i)
            = n • (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀) := by
          have hsplit : (∑ i ∈ s, α i • b i)
              = (∑ i ∈ s.erase i₀, α i • b i) + α i₀ • b i₀ :=
            (Finset.sum_erase_add s (fun i => α i • b i) hi₀).symm
          rw [hsplit] at hsum
          have hfac : n • (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀)
              = n • u - α i₀ • b i₀ := by
            rw [smul_sub, ← mul_smul, ← hα]
          rw [hfac]
          exact eq_sub_of_add_eq hsum
        have hpos : 0 < m := by
          rw [← hcard]
          exact Finset.card_pos.mpr hne
        have hcard' : (s.erase i₀).card < m := by
          rw [Finset.card_erase_of_mem hi₀, hcard]
          exact Nat.sub_lt hpos Nat.one_pos
        have hrec := ih (s.erase i₀).card hcard'
          (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀) (s.erase i₀) α rfl hstep
        have husplit : u = (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀)
            + (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀ := by abel
        rw [husplit]
        exact Submodule.add_mem _ hrec
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i₀)))
  have hsum : (∑ i ∈ c.support, c i • b i) = n • v := by
    rw [← Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (fun i r => r • b i) (by simp)]
    exact hc
  exact key c.support.card v c.support (fun i => c i) rfl hsum

/-! ## The coordinatewise quotient by `n` -/

/-- The element of `ℤ⟨X⟩` obtained by dividing every coefficient of `a` by `n`. -/
private noncomputable def divCoeff (X : Type*) (n : ℤ) (a : Work.SSGRoute.prop5.FreeAssoc X) :
    Work.SSGRoute.prop5.FreeAssoc X :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun c => c / n) (by simp))

private theorem divCoeff_coeff (X : Type*) (n : ℤ) (a : Work.SSGRoute.prop5.FreeAssoc X)
    (w : FreeMonoid X) : (divCoeff X n a).coeff w = a.coeff w / n := by
  rw [divCoeff, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply]

/-! ## Saturation of the degree-`j` Hall span -/

theorem hallSpan_saturated (X : Type) [LinearOrder X] (j : ℕ) (n : ℤ) (hn : n ≠ 0)
    (a : Work.SSGRoute.prop5.FreeAssoc X)
    (ha : a ∈ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
      ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
        Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h})
    (hdiv : ∀ w : FreeMonoid X, n ∣ a.coeff w) :
    ∃ b ∈ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
      ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
        Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h},
      a = n • b := by
  classical
  -- the set of generators, written as the range of the (foliage-injective) Hall family
  have hrange : {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h}
      = Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.monBrk X h.1) := by
    ext b
    constructor
    · rintro ⟨h, hh, hs, rfl⟩
      exact ⟨⟨h, hh, hs⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2, rfl⟩
  have hle₁ : Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h}
      ≤ Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.monBrk X h.1)) :=
    Submodule.span_mono (by rw [hrange])
  have hle₂ : Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
        Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
          Work.SSGRoute.prop5.monBrk X h.1))
      ≤ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h} :=
    Submodule.span_mono (by rw [← hrange])
  have haR : a ∈ Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
      Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
        Work.SSGRoute.prop5.monBrk X h.1)) := hle₁ ha
  -- divide the coefficients of `a` by `n`
  have hmul : ∀ w : FreeMonoid X, n * (divCoeff X n a).coeff w = a.coeff w := by
    intro w
    rw [divCoeff_coeff]
    exact Int.mul_ediv_cancel' (hdiv w)
  have ham : a = n • divCoeff X n a := by
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.coeff_smul]
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact (hmul w).symm
  -- purity of the Hall span, applied to the unitriangular family of bracket monomials
  have hmR : divCoeff X n a ∈ Submodule.span ℤ (Set.range (fun h :
      {h : Work.SSGRoute.prop5.Magma X //
        Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
          Work.SSGRoute.prop5.monBrk X h.1)) :=
    hallSpan_pure_of_leading
      (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.Magma.foliage h.1)
      (fun h₁ h₂ hfol => Subtype.ext
        (Work.SSGRoute.prop5.witt.hall_foliage_injective_aux h₁.2.1 h₂.2.1 hfol))
      (fun h => Work.SSGRoute.prop5.monBrk X h.1)
      (fun h => (monBrk_coeffF_lead h.2.1).1)
      (fun h w hw => (monBrk_coeffF_lead h.2.1).2 w hw)
      n hn (divCoeff X n a) (by rw [← ham]; exact haR)
  exact ⟨divCoeff X n a, hle₂ hmR, ham⟩

end Work.SSGRoute
