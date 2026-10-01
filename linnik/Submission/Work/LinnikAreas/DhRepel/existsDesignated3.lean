import Mathlib
import Submission.Work.LinnikAreas.DhRepel.Defs
import Submission.Work.LinnikAreas.DhRepel.farZeroLambdaLower
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.LinnikAreas.DhRepel

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option autoImplicit false

/-- **Existence of a designated second-minimal pair of zeros.**

There is an absolute constant `c > 0` such that for all sufficiently large moduli `q` the following
holds.  Let `χ₀` be a real character of level `q` (`χ₀ ^ 2 = 1`) with a real exceptional zero `ρ₀`
of minimal `λ` (this is the content of `IsMin1`), and let `(χ, ρ)` be a zero of another character
(`χ ≠ χ₀`, `χ ≠ 1`) with `|Im ρ| ≤ 1`.  Then either `λ(ρ) ≥ c`, or `χ₀` has another zero `ρ'` in
the strip `|Im| ≤ 1` with strictly smaller `λ`, or there is a pair `(χ₂, ρ₂)`, `χ₂ ≠ χ₀`, `χ₂ ≠ 1`,
which minimises `λ` among all zeros of non-principal characters in the ball
`|Im u| ≤ |Im ρ₂| + 1` (except for the pair `(χ₀,ρ₀)`) and satisfies `λ(ρ₂) ≤ λ(ρ)`.

The proof picks the minimiser `(χ₂,ρ₂)` of `λ` over all zeros `u` of non-principal characters with
`|Im u| ≤ 2` and `Re u ≥ Re ρ` (a finite set), and splits into cases: if `χ₂ ≠ χ₀` it is the
designated pair (the far zero-free region `farZeroLambdaLower` shows `|Im ρ₂| < 1`, so the ball
`|Im u| ≤ |Im ρ₂| + 1` is contained in the strip `|Im u| ≤ 2` on which `(χ₂,ρ₂)` is minimal); if
`χ₂ = χ₀` either `λ(ρ₂) < λ(ρ)`, giving the second alternative, or `λ(ρ₂) = λ(ρ)`, and then `(χ,ρ)`
itself is a designated pair. -/
theorem existsDesignated3 : ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₀ : DirichletCharacter ℂ q) (ρ₀ : ℂ),
    Work.LinnikContract.IsMin1 χ₀ ρ₀ → χ₀ ^ 2 = 1 → ρ₀.im = 0 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), χ ≠ χ₀ → χ ≠ 1 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → ρ ≠ ρ₀ →
      (c ≤ Work.LinnikContract.lamOf q ρ) ∨
      (∃ ρ' : ℂ, Work.LinnikContract.zeroMult χ₀ ρ' ≠ 0 ∧ |ρ'.im| ≤ 1 ∧ ρ' ≠ ρ₀ ∧
        Work.LinnikContract.lamOf q ρ' < Work.LinnikContract.lamOf q ρ) ∨
      (∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
        χ₂ ≠ χ₀ ∧ χ₂ ≠ 1 ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧ |ρ₂.im| ≤ 1 ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
        ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
          |u.im| ≤ |ρ₂.im| + 1 → (ψ, u) ≠ (χ₀, ρ₀) →
            Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) := by
  obtain ⟨c, hcpos, q₀, hfar⟩ := farZeroLambdaLower
  refine ⟨c, hcpos, max q₀ 6, ?_⟩
  intro q hq hqne χ₀ ρ₀ _hmin1 _hsq _hρ₀im χ ρ hχχ₀ hχ1 hzm himρ _hneρ₀
  have hq₀ : q₀ ≤ q := le_trans (le_max_left q₀ 6) hq
  have hq6 : 6 ≤ q := le_trans (le_max_right q₀ 6) hq
  haveI : NeZero q := hqne
  have hlogpos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show (1 : ℕ) < q by omega))
  rcases le_or_gt c (Work.LinnikContract.lamOf q ρ) with hle | hlt
  · exact Or.inl hle
  -- From here on `lamOf q ρ < c`.
  -- The finite set of candidate pairs (zeros in the strip `|Im| ≤ 2`, real part at least `ρ.re`,
  -- the pair `(χ₀,ρ₀)` excluded) over which `lamOf` is minimised.
  let T : Set (DirichletCharacter ℂ q × ℂ) :=
    {p | p.1 ≠ 1 ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧ ρ.re ≤ p.2.re ∧
      |p.2.im| ≤ 2 ∧ p ≠ (χ₀, ρ₀)}
  have hTmem : ∀ p : DirichletCharacter ℂ q × ℂ, p ∈ T ↔
      p.1 ≠ 1 ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧ ρ.re ≤ p.2.re ∧
      |p.2.im| ≤ 2 ∧ p ≠ (χ₀, ρ₀) := fun _ => Iff.rfl
  have hTfin : T.Finite := by
    have hsup : (⋃ ψ : DirichletCharacter ℂ q,
        (fun u : ℂ => (ψ, u)) '' {u : ℂ | Work.LinnikContract.zeroMult ψ u ≠ 0 ∧
          ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 2}).Finite := by
      refine Set.finite_iUnion (f := fun ψ => (fun u : ℂ => (ψ, u)) '' {u : ℂ |
        Work.LinnikContract.zeroMult ψ u ≠ 0 ∧ ρ.re ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ 2}) ?_
      intro ψ
      exact (boxMaxZeroAux.finite_zeroMult_box ψ ρ.re 2).image (fun u => (ψ, u))
    refine Set.Finite.subset hsup ?_
    rintro p hp
    obtain ⟨ψ, u⟩ := p
    obtain ⟨_hp1, hp2, hp3, hp4, _hp5⟩ := (hTmem (ψ, u)).mp hp
    refine Set.mem_iUnion.mpr ⟨ψ, ?_⟩
    rw [Set.mem_image]
    exact ⟨u, ⟨hp2, hp3, le_of_lt (boxMaxZeroAux.zeroMult_re_lt_one ψ hp2), hp4⟩, rfl⟩
  have hTχρ : (χ, ρ) ∈ T :=
    (hTmem (χ, ρ)).mpr ⟨hχ1, hzm, le_refl _, by linarith, fun h => hχχ₀ (congrArg Prod.fst h)⟩
  have hTne : T.Nonempty := ⟨(χ, ρ), hTχρ⟩
  obtain ⟨p₂, hp₂mem, hmin⟩ :=
    Finset.exists_min_image hTfin.toFinset (fun p => Work.LinnikContract.lamOf q p.2)
      (hTfin.toFinset_nonempty.mpr hTne)
  obtain ⟨χ₂, ρ₂⟩ := p₂
  have hp₂T : (χ₂, ρ₂) ∈ T := (Set.Finite.mem_toFinset hTfin).mp hp₂mem
  obtain ⟨hp₂χ1, hp₂zm, _hp₂re, hp₂im, hp₂ne⟩ := (hTmem (χ₂, ρ₂)).mp hp₂T
  have hleρ : Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ :=
    hmin (χ, ρ) ((Set.Finite.mem_toFinset hTfin).mpr hTχρ)
  -- Minimality of `lamOf q ρ₂` among *all* zeros of non-principal characters in the strip
  -- `|Im| ≤ 2` (other than `(χ₀,ρ₀)`).
  have hQ : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 → (ψ, u) ≠ (χ₀, ρ₀) →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
    intro ψ u hψ hzmu himu hne
    by_contra hcon
    have hlt2 : Work.LinnikContract.lamOf q u < Work.LinnikContract.lamOf q ρ₂ :=
      not_le.mp hcon
    have hltρ : Work.LinnikContract.lamOf q u < Work.LinnikContract.lamOf q ρ :=
      lt_of_lt_of_le hlt2 hleρ
    have hure : ρ.re < u.re := by
      have h1 : (1 - u.re) * Real.log (q : ℝ) < (1 - ρ.re) * Real.log (q : ℝ) := by
        simpa only [Work.LinnikContract.lamOf] using hltρ
      have h2 : 1 - u.re < 1 - ρ.re := (mul_lt_mul_iff_left₀ hlogpos).mp h1
      linarith
    have huT : (ψ, u) ∈ T := (hTmem (ψ, u)).mpr ⟨hψ, hzmu, le_of_lt hure, himu, hne⟩
    have hmin' := hmin (ψ, u) ((Set.Finite.mem_toFinset hTfin).mpr huT)
    linarith
  -- The far zero-free region forces `|Im ρ₂| ≤ 1`: `lamOf q ρ₂ ≤ lamOf q ρ < c`.
  have himρ₂ : |ρ₂.im| ≤ 1 := by
    by_contra hcon
    have h1 : 1 < |ρ₂.im| := not_le.mp hcon
    have h4 : |ρ₂.im| ≤ 4 := by linarith
    have hc := hfar q hq₀ χ₂ hp₂χ1 ρ₂ hp₂zm (le_of_lt h1) h4
    linarith
  by_cases hχ₂χ₀ : χ₂ ≠ χ₀
  · -- a zero of an *other* character which is minimal in the ball
    refine Or.inr (Or.inr ⟨χ₂, ρ₂, hχ₂χ₀, hp₂χ1, hp₂zm, himρ₂, hleρ, ?_⟩)
    intro ψ u hψ hzmu himu hne
    exact hQ ψ u hψ hzmu (by linarith [abs_nonneg ρ₂.im, himρ₂, himu]) hne
  · have hχ₂eq : χ₂ = χ₀ := not_not.mp hχ₂χ₀
    rcases lt_or_eq_of_le hleρ with hltρ₂ | heq
    · -- a *strictly* smaller zero of `χ₀`
      refine Or.inr (Or.inl ⟨ρ₂, ?_, himρ₂, ?_, hltρ₂⟩)
      · rw [← hχ₂eq]
        exact hp₂zm
      · intro h
        exact hp₂ne (Prod.ext hχ₂eq h)
    · -- minimality is attained at `(χ,ρ)` itself
      refine Or.inr (Or.inr ⟨χ, ρ, hχχ₀, hχ1, hzm, himρ, le_refl _, ?_⟩)
      intro ψ u hψ hzmu himu hne
      have h := hQ ψ u hψ hzmu (by linarith [abs_nonneg ρ.im, himρ, himu]) hne
      exact heq ▸ h

end

end Work.LinnikAreas.DhRepel
