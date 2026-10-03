import Mathlib
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.halfAtPrelude
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.rho_magnet
import Submission.Work.OROneRel.ne_one_of_not_isProperPower
import Submission.Work.OROneRel.freiheitssatz_at
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow
import Submission.Work.OROneRel.magRew_block_subword_mmBeta
import Submission.Work.OROneRel.relatorNorm_mmW_letterCountNot
import Submission.Work.OROneRel.relatorNorm_magRewRel_eq_of_notMem
import Submission.Work.OROneRel.expSum_ofAdd_wordEps
import Submission.Work.OROneRel.letterCountNot_lt_of_isSubwordOf_half
import Submission.Work.OROneRel.relatorNorm_magRewRel_letterCountNot
import Submission.Work.OROneRel.weinbaum_half_noZero

/-!
# The half-length case of Weinbaum's theorem, with a letter of exponent sum zero

`Work.OROneRel.weinbaum_sigma_zero_half` is the "engine" case of Weinbaum's theorem: for a cyclically
reduced relator `R` which is not a proper power and has a letter `z` of exponent sum zero, every
nontrivial subword `w` of a power of `R` with `2 * |w| <= |R|` is nontrivial in `⟨β | R⟩`.

## The plan

The half-length statement is proved for *every* relator by strong induction on `relatorNorm`, split
into two cases at each relator `S`:

* **`z` has exponent sum zero in `S` (this file, `sigma_step`).**  `⟨β | S⟩` is an HNN extension of
  the one-relator group `⟨mmBeta z S | mmW z S⟩` on the decorated letters (`mmStepData_of_expsum_zero`,
  `mmTheta`/`mmPsi`), with stable letter `z`.  A counterexample `w` at `S` satisfies `σ_z w = 0`
  (abelianisation criterion), hence its Magnus rewriting `(magnusMap z)^{-1} w` lies in the base: this
  is `magRew_block_subword_mmBeta` (`Submission.Work.OROneRel.magRew_block_subword_mmBeta`), which
  localises the rewriting of a subword to a subword of a power of the rewritten relator.  The
  rewriting is strictly shorter (`letterCountNot_lt_of_isSubwordOf_half`), so the complement argument
  (`exists_complement_of_isSubwordOf_pow`) and the induction hypothesis at the rewritten relator give
  a contradiction.

* **no letter of `S` has exponent sum zero (`weinbaum_half_noZero`).**  Magnus' substitution trick
  (`subst t x p q`, `t ↦ t ^ p`, `x ↦ x * t ^ (-q)`) transports a counterexample to a counterexample
  at the cyclically reduced conjugate of the substituted relator, whose Magnus rewriting is strictly
  shorter; then the previous case applies.

## Main declarations

* `Work.OROneRel.HalfAt` : the half-length statement at a relator;
* `Work.OROneRel.sigma_step` : the exponent-sum-zero step;
* `Work.OROneRel.weinbaum_sigma_zero_half` : the requested statement.
-/

namespace Work.OROneRel

universe u

/-- The exponent sum `expSum z` of an element, as a homomorphism into `Multiplicative ℤ`, is the
exponent sum computed on its reduced word (in additive form). -/
theorem expSum_eq_ofAdd_wordEps {α : Type u} [DecidableEq α] (z : α) (w : FreeGroup α) :
    expSum z w = Multiplicative.ofAdd (wordEps z w.toWord) :=
  Work.OROneRel.expSum_ofAdd_wordEps z w

/-- The exponent sum of `z` in a relator `R` is zero (written `expSum z R = 1`, the exponent sum
being an element of the multiplicative group `Multiplicative ℤ`) if and only if `eps z R = 0`. -/
theorem eps_eq_zero_of_expSum_eq_one {α : Type u} {z : α} {R : FreeGroup α}
    (h : expSum z R = 1) : eps z R = 0 := by
  classical
  have h1 : Multiplicative.ofAdd (wordEps z R.toWord) = (1 : Multiplicative ℤ) := by
    rw [← expSum_eq_ofAdd_wordEps z R, h]
  have h2 : wordEps z R.toWord = 0 := Multiplicative.ofAdd.injective (by simpa using h1)
  simpa only [eps] using h2

/-- A counterexample is annihilated by every homomorphism which kills the relator: if `w` is trivial
in `⟨β | R⟩` then the exponent sum of `z` in `w` is an integral power of that in `R`; in particular
`σ_z w = 0` when `σ_z R = 0`. -/
theorem expSum_eq_one_of_mk_eq_one {α : Type u} (R w : FreeGroup α) {z : α}
    (hz : expSum z R = 1) (h : PresentedGroup.mk ({R} : Set (FreeGroup α)) w = 1) :
    expSum z w = 1 := by
  have hmem : w ∈ Subgroup.normalClosure ({R} : Set (FreeGroup α)) :=
    (PresentedGroup.mk_eq_one_iff).mp h
  obtain ⟨k, hk⟩ := expSum_eq_zpow_of_mem_normalClosure z hmem
  rw [hk, hz, one_zpow]

/-- **The Magnus rewriting of a relator which is not a proper power is not a proper power.**  This is
`rho_magnet`: the rewriting represents the relator in the conjugates `z ^ i * x * z ^ (-i)`, so a
proper power decomposition of the rewriting descends to one of the relator itself. -/
theorem not_isProperPower_magRewRel {α : Type u} {R : FreeGroup α} (z : α)
    (hpp : ¬ IsProperPower R) (h : eps z R = 0) : ¬ IsProperPower (magRewRel z R) := by
  classical
  rintro ⟨u, m, hm, hu⟩
  refine hpp ⟨rho z u, m, hm, ?_⟩
  have h1 : rho z (magRewRel z R) = R := by
    rw [show magRewRel z R = magnet R z from by
      rw [magRewRel, magnet, magRew_zero_eq_rewrite]]
    exact rho_magnet R z h
  rw [← h1, hu, map_pow]


/-- The induction hypothesis in the shape consumed by the assembly: the half-length statement at the
Magnus rewriting of `T` together with the exponent-sum-zero step gives the half-length statement
at `T`. -/
theorem halfAt_of_sigma_step
    (hσstep : ∀ {γ : Type u} (T : FreeGroup γ) {y : γ}, IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → y ∈ relatorLetters T → expSum y T = 1 → HalfAt (mmW y T) → HalfAt T) :
    ∀ {γ : Type u} (T : FreeGroup γ) {y : γ}, IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → y ∈ relatorLetters T → expSum y T = 1 →
      (∀ {δ : Type u} (U : FreeGroup δ), relatorNorm U < relatorNorm T →
        IsCyclicallyReducedRelator U → ¬ IsProperPower U → HalfAt U) → HalfAt T := by
  intro γ T y hc hp hy hyσ IH
  refine hσstep T hc hp hy hyσ ?_
  have hε : eps y T = 0 := eps_eq_zero_of_expSum_eq_one hyσ
  exact IH (mmW y T) (mmW_relatorNorm_lt hy) (mmW_isCyclicallyReduced hc hε)
    (not_isProperPower_mmW hp hε)

/-- **The body of the exponent-sum-zero step**, with the three citations it rests on as explicit
hypotheses (they are proved elsewhere: the localisation
`Submission.Work.OROneRel.magRew_block_subword_mmBeta`, the strict length drop
`Submission.Work.OROneRel.letterCountNot_lt_half_standalone` and the norm of the rewritten relator
`Submission.Work.OROneRel.relatorNorm_mmW_letterCountNot`). -/
theorem sigma_step_aux {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R)
    (hz : z ∈ relatorLetters R) (hσ : expSum z R = 1)
    (hM : HalfAt (mmW z R))
    (hloc : ∀ (k : ℕ) (w : FreeGroup β), IsSubwordOf w (R ^ k) → eps z R = 0 →
      ∃ (j : ℤ) (u : FreeGroup (mmBeta z R)),
        IsSubwordOf u ((mmW z R) ^ k) ∧
        FreeGroup.map (fun p : mmBeta z R => ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u
          = magShiftAut z j (magRewRel z w) ∧
        (FreeGroup.toWord u).length = letterCountNot z w)
    (hdrop : ∀ (k : ℕ) (w : FreeGroup β), IsSubwordOf w (R ^ k) →
      2 * relatorNorm w ≤ relatorNorm R → w ≠ 1 →
      letterCountNot z w < letterCountNot z R)
    (hnorm : relatorNorm (mmW z R) = letterCountNot z R)
    (k : ℕ) (w : FreeGroup β) (hsub : IsSubwordOf w (R ^ k))
    (hhalf : 2 * relatorNorm w ≤ relatorNorm R) (hw1 : w ≠ 1)
    (hcontra : PresentedGroup.mk ({R} : Set (FreeGroup β)) w = 1) : False := by
  classical
  have hR1 : R ≠ 1 := ne_one_of_not_isProperPower hpp
  have hε : eps z R = 0 := eps_eq_zero_of_expSum_eq_one hσ
  have hσw : expSum z w = 1 := expSum_eq_one_of_mk_eq_one R w hσ hcontra
  have hεw : eps z w = 0 := eps_eq_zero_of_expSum_eq_one hσw
  -- the localisation: the rewriting of the arc is a subword of a power of the rewritten relator
  obtain ⟨j, u, hsub', hu, hlen⟩ := hloc k w hsub hε
  -- the descent: the rewriting is trivial in the Magnus base
  have hmu : PresentedGroup.mk ({mmW z R} : Set (FreeGroup (mmBeta z R))) u = 1 :=
    mk_mmW_eq_one_of_mk_eq_one w hR1 hz hε hcyc hεw hcontra j u hu
  -- the rewriting is nontrivial
  have hu1 : u ≠ 1 := by
    intro hu0
    have h1 : magShiftAut z j (magRewRel z w) = 1 := by rw [← hu, hu0, map_one]
    have h2 : magRewRel z w = 1 := (magShiftAut z j).injective (by rwa [map_one])
    have h3 : rho z (magRewRel z w) = w := by
      rw [show magRewRel z w = magnet w z from by
        rw [magRewRel, magnet, magRew_zero_eq_rewrite]]
      exact rho_magnet w z hεw
    rw [h2, map_one] at h3
    exact hw1 h3.symm
  -- the rewriting is strictly shorter than the rewritten relator
  have hlenM : relatorNorm u = letterCountNot z w := by
    simpa [relatorNorm, FreeGroup.norm] using hlen
  have hlt : relatorNorm u < relatorNorm (mmW z R) := by
    rw [hlenM, hnorm]
    exact hdrop k w hsub hhalf hw1
  -- cutting out the complementary arc of the rewritten relator and applying the induction hypothesis
  have hcycM : IsCyclicallyReducedRelator (mmW z R) := mmW_isCyclicallyReduced hcyc hε
  obtain ⟨s, m, hsubs, hs1, hsnorm, hscontra⟩ :=
    exists_complement_counterexample hcycM hsub' hlt hu1 hmu
  have hsum : relatorNorm u + relatorNorm s = relatorNorm (mmW z R) := by omega
  rcases le_total (relatorNorm u) (relatorNorm s) with h | h
  · exact hM k u hsub' (by omega) hu1 hmu
  · exact hM m s hsubs (by omega) hs1 hscontra

/-- The exponent-sum-zero step of the induction.  If `z` occurs in the cyclically reduced relator `R`
with exponent sum zero, `R` is not a proper power, and the half-length statement holds at the Magnus
rewriting `mmW z R` of `R` with respect to `z`, then it holds at `R`. -/
theorem sigma_step {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R)
    (hz : z ∈ relatorLetters R) (hσ : expSum z R = 1)
    (hM : HalfAt (mmW z R))
    (k : ℕ) (w : FreeGroup β) (hsub : IsSubwordOf w (R ^ k))
    (hhalf : 2 * relatorNorm w ≤ relatorNorm R) (hw1 : w ≠ 1)
    (hcontra : PresentedGroup.mk ({R} : Set (FreeGroup β)) w = 1) : False := by
  refine sigma_step_aux R hcyc hpp hz hσ hM ?_ ?_ ?_ k w hsub hhalf hw1 hcontra
  · -- the localisation of the Magnus rewriting of the subword
    intro k' w' hsub' hε'
    exact magRew_block_subword_mmBeta R z hcyc hε' hsub'
  · -- the strict drop of the number of letters different from `z`
    intro k' w' hsub' hhalf' hw1'
    exact letterCountNot_lt_of_isSubwordOf_half R w' z k' hcyc hpp hz hσ hsub' hhalf' hw1'
  · -- the norm of the rewritten relator
    exact relatorNorm_mmW_letterCountNot z R hcyc (eps_eq_zero_of_expSum_eq_one hσ)

/-- **Assembly of the induction.**  If the exponent-sum-zero step and the no-zero-exponent-sum step
are available, then the half-length statement holds for every cyclically reduced relator which is not
a proper power. -/
theorem halfAt_all {β : Type u} (R : FreeGroup β)
    (hstep : ∀ {γ : Type u} (T : FreeGroup γ) {y : γ}, IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → y ∈ relatorLetters T → expSum y T = 1 →
      (∀ {δ : Type u} (U : FreeGroup δ), relatorNorm U < relatorNorm T →
        IsCyclicallyReducedRelator U → ¬ IsProperPower U → HalfAt U) → HalfAt T)
    (hnozero : ∀ {γ : Type u} (T : FreeGroup γ), IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → (∀ y ∈ relatorLetters T, expSum y T ≠ 1) →
      (∀ {δ : Type u} (U : FreeGroup δ), relatorNorm U < relatorNorm T →
        IsCyclicallyReducedRelator U → ¬ IsProperPower U → HalfAt U) → HalfAt T)
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R) : HalfAt R := by
  classical
  suffices main : ∀ n : ℕ, ∀ (γ : Type u) (T : FreeGroup γ), relatorNorm T ≤ n →
      IsCyclicallyReducedRelator T → ¬ IsProperPower T → HalfAt T from
    main (relatorNorm R) β R le_rfl hcyc hpp
  intro n
  induction n with
  | zero =>
      intro γ T hT hc hp
      exfalso
      have h0 : relatorNorm T = 0 := Nat.le_zero.mp hT
      have h1 : T = 1 := by
        have : FreeGroup.norm T = 0 := by simpa [relatorNorm] using h0
        exact FreeGroup.norm_eq_zero.mp this
      exact hp (h1 ▸ isProperPower_one)
  | succ n ih =>
      intro γ T hT hc hp
      by_cases h : ∃ y ∈ relatorLetters T, expSum y T = 1
      · obtain ⟨y, hy, hyσ⟩ := h
        refine hstep T hc hp hy hyσ (fun U hU hcU hpU => ?_)
        exact ih _ U (by omega) hcU hpU
      · push Not at h
        refine hnozero T hc hp h (fun U hU hcU hpU => ?_)
        exact ih _ U (by omega) hcU hpU

/-- **The no-zero-exponent-sum case of the induction**, assembled.  The counterexample at the
cyclically reduced relator `T` (in which every letter has nonzero exponent sum) is transported by
Magnus' substitution to the cyclically reduced conjugate `v` of the substituted relator, with the
measure bound `relatorNorm (magRewRel t v) < relatorNorm T`.  Cutting out the complementary arc of `v`
produces a half-length counterexample at `v`, and then there are two cases:

* if `t` occurs in `v`: the exponent-sum-zero step `sigma_step_aux` applies at `v`, its remaining
  hypothesis `HalfAt (mmW t v)` coming from the induction hypothesis (the measure bound
  `relatorNorm (mmW t v) = letterCountNot t v = relatorNorm (magRewRel t v) < relatorNorm T`);
* if `t` does not occur in `v`: the rewriting deletes nothing
  (`relatorNorm_magRewRel_eq_of_notMem`), so `relatorNorm v < relatorNorm T` and the induction
  hypothesis at `v` itself closes the counterexample. -/
theorem halfAt_noZero_aux {β : Type u} (T : FreeGroup β)
    (hloc : ∀ {δ : Type u} (S : FreeGroup δ) (y : δ) {k : ℕ} {v : FreeGroup δ},
      IsCyclicallyReducedRelator S → eps y S = 0 → IsSubwordOf v (S ^ k) →
      ∃ (j : ℤ) (u : FreeGroup (mmBeta y S)),
        IsSubwordOf u ((mmW y S) ^ k) ∧
        FreeGroup.map (fun p : mmBeta y S => ((p.1.1, p.1.2) : ({x : δ // x ≠ y} × ℤ))) u
          = magShiftAut y j (magRewRel y v) ∧
        (FreeGroup.toWord u).length = letterCountNot y v)
    (hdrop : ∀ {δ : Type u} (S : FreeGroup δ) (y : δ) (k : ℕ) (w : FreeGroup δ),
      IsCyclicallyReducedRelator S → ¬ IsProperPower S → y ∈ relatorLetters S → expSum y S = 1 →
      IsSubwordOf w (S ^ k) → 2 * relatorNorm w ≤ relatorNorm S → w ≠ 1 →
      letterCountNot y w < letterCountNot y S)
    (hmag : ∀ {δ : Type u} (S : FreeGroup δ) (y : δ),
      relatorNorm (magRewRel y S) = letterCountNot y S)
    (hsubst : ∀ {δ : Type u} (S : FreeGroup δ), IsCyclicallyReducedRelator S →
      ¬ IsProperPower S → (∀ y ∈ relatorLetters S, expSum y S ≠ 1) →
      ∀ (k : ℕ) (w : FreeGroup δ), IsSubwordOf w (S ^ k) → 2 * relatorNorm w ≤ relatorNorm S →
      w ≠ 1 → PresentedGroup.mk ({S} : Set (FreeGroup δ)) w = 1 →
      ∃ (x t : δ), x ≠ t ∧ x ∈ relatorLetters S ∧ t ∈ relatorLetters S ∧
      ∃ (c v w' : FreeGroup δ) (k' : ℕ),
        v = c * subst t x (Multiplicative.toAdd (sigma x S)) (Multiplicative.toAdd (sigma t S)) S *
          c⁻¹ ∧
        IsCyclicallyReducedRelator v ∧ ¬ IsProperPower v ∧ expSum t v = 1 ∧
        relatorNorm (magRewRel t v) < relatorNorm S ∧
        IsSubwordOf w' (v ^ k') ∧ relatorNorm w' < relatorNorm v ∧ w' ≠ 1 ∧
        PresentedGroup.mk ({v} : Set (FreeGroup δ)) w' = 1)
    (hcyc : IsCyclicallyReducedRelator T) (hpp : ¬ IsProperPower T)
    (hσ : ∀ y ∈ relatorLetters T, expSum y T ≠ 1)
    (IH : ∀ {δ : Type u} (U : FreeGroup δ), relatorNorm U < relatorNorm T →
      IsCyclicallyReducedRelator U → ¬ IsProperPower U → HalfAt U) :
    HalfAt T := by
  intro k w hsub hhalf hw1 hcontra
  obtain ⟨x, t, hxt, hx, ht, c, v, w', k', hv, hcycv, hppv, hσtv, hmeasure, hsub', hlt', hw'1,
    hcontra'⟩ := hsubst T hcyc hpp hσ k w hsub hhalf hw1 hcontra
  -- cutting out the complementary arc of `v` produces a second counterexample at `v`
  obtain ⟨s, m, hsubs, hs1, hsnorm, hscontra⟩ :=
    exists_complement_counterexample hcycv hsub' hlt' hw'1 hcontra'
  have hsum : relatorNorm w' + relatorNorm s = relatorNorm v := by omega
  -- the two cases at `v`
  have key : ∀ (u : FreeGroup β) (k' : ℕ), IsSubwordOf u (v ^ k') → u ≠ 1 →
      PresentedGroup.mk ({v} : Set (FreeGroup β)) u = 1 →
      2 * relatorNorm u ≤ relatorNorm v → False := by
    intro u k' hsubu hu1 hcontrau hhalfu
    by_cases htmem : t ∈ relatorLetters v
    · -- `t` occurs in `v`: the exponent-sum-zero step, with the induction hypothesis at the magnet
      have hεt : eps t v = 0 := eps_eq_zero_of_expSum_eq_one hσtv
      have hmagnorm : relatorNorm (mmW t v) < relatorNorm T := by
        rw [relatorNorm_mmW_letterCountNot t v hcycv hεt, ← hmag v t]
        exact hmeasure
      exact sigma_step_aux v hcycv hppv htmem hσtv
        (IH (mmW t v) hmagnorm (mmW_isCyclicallyReduced hcycv hεt)
          (not_isProperPower_mmW hppv hεt))
        (fun k'' u'' hsub'' hε'' => hloc v t hcycv hε'' hsub'')
        (fun k'' u'' hsub'' hhalf'' hu1'' =>
          hdrop v t k'' u'' hcycv hppv htmem hσtv hsub'' hhalf'' hu1'')
        (relatorNorm_mmW_letterCountNot t v hcycv hεt) k' u hsubu hhalfu hu1 hcontrau
    · -- `t` does not occur in `v`: the rewriting deletes nothing, so `v` is itself shorter
      have hvnorm : relatorNorm v < relatorNorm T := by
        rw [← relatorNorm_magRewRel_eq_of_notMem t htmem]
        exact hmeasure
      exact IH v hvnorm hcycv hppv k' u hsubu hhalfu hu1 hcontrau
  rcases le_total (relatorNorm w') (relatorNorm s) with hle | hle
  · exact key w' k' hsub' hw'1 hcontra' (by omega)
  · exact key s m hsubs hs1 hscontra (by omega)

/-- **The requested statement, given the no-zero-exponent-sum case of the induction.**  All that is
missing from `weinbaum_sigma_zero_half` is the second case `hnozero` of the induction: the half-length
statement at a cyclically reduced relator (not a proper power) in which *no* letter has exponent sum
zero, given the same statement at every strictly shorter relator.  That case is
`Work.OROneRel.subst_transport` (Magnus' substitution trick) together with the exponent-sum-zero step
`sigma_step_aux` at the substituted relator. -/
theorem weinbaum_sigma_zero_half_of {β : Type u} (R : FreeGroup β) {z : β}
    (hnozero : ∀ {γ : Type u} (T : FreeGroup γ), IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → (∀ y ∈ relatorLetters T, expSum y T ≠ 1) →
      (∀ {δ : Type u} (U : FreeGroup δ), relatorNorm U < relatorNorm T →
        IsCyclicallyReducedRelator U → ¬ IsProperPower U → HalfAt U) → HalfAt T)
    (hcyc : IsCyclicallyReducedRelator R) (hpp : ¬ IsProperPower R)
    (hz : z ∈ relatorLetters R) (h : expSum z R = 1) :
    ∀ (k : ℕ) (w : FreeGroup β), IsSubwordOf w (R ^ k) →
      2 * relatorNorm w ≤ relatorNorm R → w ≠ 1 →
      PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1 := by
  have hσstep : ∀ {γ : Type u} (T : FreeGroup γ) {y : γ}, IsCyclicallyReducedRelator T →
      ¬ IsProperPower T → y ∈ relatorLetters T → expSum y T = 1 →
      HalfAt (mmW y T) → HalfAt T := by
    intro γ T y hc hp hy hyσ hM k w hsub hhalf hw1
    exact sigma_step T hc hp hy hyσ hM k w hsub hhalf hw1
  exact halfAt_all R (halfAt_of_sigma_step hσstep) hnozero hcyc hpp

theorem weinbaum_sigma_zero_half {β : Type u} (R : FreeGroup β) {z : β}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R)
    (hpp : ¬ Work.OROneRel.IsProperPower R)
    (hz : z ∈ Work.OROneRel.relatorLetters R) (h : Work.OROneRel.expSum z R = 1) :
    ∀ (k : ℕ) (w : FreeGroup β), Work.OROneRel.IsSubwordOf w (R ^ k) →
      2 * Work.OROneRel.relatorNorm w ≤ Work.OROneRel.relatorNorm R → w ≠ 1 →
      PresentedGroup.mk ({R} : Set (FreeGroup β)) w ≠ 1 := by
  -- The exponent-sum-zero case of the induction is `sigma_step` (proved above, from the citations
  -- `magRew_block_subword_mmBeta`, `letterCountNot_lt_isSubwordOf_half` and
  -- `relatorNorm_mmW_letterCountNot`); the no-zero-exponent-sum case is
  -- `Work.OROneRel.weinbaum_half_noZero`.
  exact weinbaum_sigma_zero_half_of R
    (fun {γ : Type u} (T : FreeGroup γ) hc hp hσT IH => weinbaum_half_noZero T IH hc hp hσT)
    hcyc hpp hz h

end Work.OROneRel
