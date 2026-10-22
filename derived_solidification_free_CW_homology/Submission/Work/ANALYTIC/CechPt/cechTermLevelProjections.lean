import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs
import Submission.Work.ANALYTIC.CechPt.LevelDefs
import Submission.Work.ANALYTIC.CechPt.binaryExp_epi
import Submission.Work.ANALYTIC.CechPt.Setup
import Submission.Work.ANALYTIC.CechPt.CechLevels
import Submission.Work.ANALYTIC.CechPt.ofDigitsTruncBound
import Submission.Work.ANALYTIC.CechPt.exists_cechTerm_of_compat
import Submission.Work.ANALYTIC.CechPt.exists_compat_extension

/-!
# The level structure on the terms of the Čech nerve of the binary expansion

`Work.ANALYTIC.CechPt.cechTerm p` is the light profinite set of `(p+1)`-tuples of points of the
Cantor set `C = {0,1}^ℕ` with the same binary expansion (the `p`-th term of the Čech nerve of the
binary expansion `C ⟶ [0,1]`).

This module exhibits `cechTerm p` as the inverse limit of the finite sets
`Level.lev (2^(n+1)) p` (the level-`n` dyadic nerves of the interval) by constructing explicit
level projections

`lvlOf p n : cechTerm p ⟶ Level.lev (2^(n+1)) p`

which truncate every coordinate to its first `n+1` binary digits.  They are surjective, compatible
with the division maps `v ↦ v / 2`, jointly injective, and every locally constant `ℤ`-valued
function on `cechTerm p` factors through one of them.  These four properties are
`cechTermLevelProjections` below; they are the input to the identification
`solidDual (cechTerm p) ≅ lim_n ℤ[Level.lev (2^(n+1)) p]` used in
`Work.ANALYTIC.profinite_HI_pt`.

The mathematical content is:

* the truncation of a point of `C` to `n+1` digits is computed by `truncOf` and lies in
  `{0, …, 2^(n+1)-1}`; the digit sequences of two points of `C` with the same binary expansion
  have truncations differing by at most one (`truncVal_le_of_binExp_eq`, from
  `2^(n+1) * ofDigits d = truncOf n d + θ` with `θ ∈ [0,1]`), so that the level projections land
  in the level nerves (whose simplices have diameter at most one);
* a compatible family of level-`n` nerves is realised by a point of `cechTerm p`
  (`lvlOf_surjective`, via `exists_compat_extension` and `exists_cechTerm_of_compat`);
* the level projections are locally constant (`isLocallyConstant_lvlOf`), and a nested
  compactness argument (`exists_level_of_locallyConstant`) shows that every locally constant
  `ℤ`-valued function factors through some level.
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC.CechPt

theorem truncVal_step (j : ℕ) (c : ↥cantor) : truncVal (j + 1) c / 2 = truncVal j c := by
  rw [truncVal, truncVal, truncOf_succ_div]

theorem truncVal_div_pow (k m : ℕ) (c : ↥cantor) :
    truncVal m c = truncVal (m + k) c / 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega, pow_succ', ← Nat.div_div_eq_div_mul,
      truncVal_step, ih]

theorem truncVal_div (n m : ℕ) (h : m ≤ n) (c : ↥cantor) :
    truncVal m c = truncVal n c / 2 ^ (n - m) := by
  rw [show n = m + (n - m) by omega, show m + (n - m) - m = n - m by omega,
    ← truncVal_div_pow (n - m) m c]

theorem cantor_ext {a b : ↥cantor} (h : ∀ n, digitsOf a n = digitsOf b n) : a = b := by
  let fa : pt ⟶ cantor := CompHausLike.ofHom _ ⟨fun _ => a, continuous_const⟩
  let fb : pt ⟶ cantor := CompHausLike.ofHom _ ⟨fun _ => b, continuous_const⟩
  have key : fa = fb := by
    apply Pi.hom_ext
    intro n
    ext z
    exact h n
  exact ConcreteCategory.congr_hom key (0 : ↥pt)

theorem cechTerm_nonempty (p : ℕ) : Nonempty ↥(cechTerm p) := by
  obtain ⟨c, -⟩ := exists_coord_eq (fun _ => (0 : Fin 2))
  exact ⟨⟨fun _ => c, mem_cechCover.mpr fun i j => rfl⟩⟩

theorem cechTerm_ext {p : ℕ} {x y : ↥(cechTerm p)} (h : ∀ i, x.1 i = y.1 i) : x = y := by
  apply Subtype.ext
  exact funext h

variable {p : ℕ}

theorem truncVal_le_of_binExp_eq (x : ↥(cechTerm p)) (n : ℕ) (i j : Fin (p+1)) :
    truncVal n (x.1 i) ≤ truncVal n (x.1 j) + 1 := by
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := (ofDigitsTruncBound n (digitsOf (x.1 i)) (digitsOf (x.1 j))).1
  obtain ⟨θ', hθ0', hθ1', hθ'⟩ := (ofDigitsTruncBound n (digitsOf (x.1 j)) (digitsOf (x.1 i))).1
  have heq : Real.ofDigits (digitsOf (x.1 i)) = Real.ofDigits (digitsOf (x.1 j)) := by
    have h := congrArg (fun t : ↥unitInterval => (t : ℝ)) (cechTerm_apply_eq p x i j)
    simpa [binExp_coe] using h
  have hle : ((truncVal n (x.1 i) : ℕ) : ℝ) ≤ ((truncVal n (x.1 j) : ℕ) : ℝ) + 1 := by
    have hA : ((truncVal n (x.1 i) : ℕ) : ℝ)
        = 2 ^ (n + 1) * Real.ofDigits (digitsOf (x.1 i)) - θ := by
      rw [truncVal]; linarith
    have hB : ((truncVal n (x.1 j) : ℕ) : ℝ)
        = 2 ^ (n + 1) * Real.ofDigits (digitsOf (x.1 j)) - θ' := by
      rw [truncVal]; linarith
    rw [hA, hB, heq]; linarith
  exact_mod_cast hle

/-- The level map (definition). -/
def lvlOf (p n : ℕ) (x : ↥(cechTerm p)) : Level.lev (2 ^ (n + 1)) p :=
  ⟨fun i => ⟨truncVal n (x.1 i), truncOf_lt n (digitsOf (x.1 i))⟩,
    fun i j => truncVal_le_of_binExp_eq x n i j⟩

theorem lvlOf_apply (p n : ℕ) (x : ↥(cechTerm p)) (i : Fin (p+1)) :
    ((lvlOf p n x).1 i : ℕ) = truncVal n (x.1 i) := by
  simp only [lvlOf, truncVal]

theorem lvlOf_compat (p n : ℕ) (x : ↥(cechTerm p)) (i : Fin (p+1)) :
    ((lvlOf p (n+1) x).1 i : ℕ) / 2 = ((lvlOf p n x).1 i : ℕ) := by
  rw [lvlOf_apply, lvlOf_apply, truncVal_step]

theorem lvlOf_injective (p : ℕ) {x y : ↥(cechTerm p)} (h : ∀ n, lvlOf p n x = lvlOf p n y) :
    x = y := by
  apply cechTerm_ext
  intro i
  apply cantor_ext
  intro k
  have hk : truncVal k (x.1 i) = truncVal k (y.1 i) := by
    have := congrArg (fun t : Level.lev (2 ^ (k+1)) p => ((t.1 i : Fin (2^(k+1))) : ℕ)) (h k)
    rw [lvlOf_apply, lvlOf_apply] at this
    exact this
  apply Fin.ext
  rw [← truncOf_mod_two k (digitsOf (x.1 i)), ← truncOf_mod_two k (digitsOf (y.1 i))]
  simpa only [truncVal] using congrArg (· % 2) hk



@[simp] theorem cechProj_hom (p : ℕ) (j : Fin (p+1)) (x : ↥(cechTerm p)) :
    ConcreteCategory.hom (cechProj p j) x = x.1 j := cechProj_apply p j x

@[simp] theorem coord_hom (k : ℕ) (c : ↥cantor) :
    ConcreteCategory.hom (coord k) c = digitsOf c k := rfl

theorem truncVal_congr {n : ℕ} {c c' : ↥cantor} (h : ∀ k ≤ n, digitsOf c k = digitsOf c' k) :
    truncVal n c = truncVal n c' := by
  rw [truncVal, truncVal, truncOf, truncOf]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [h k (by omega)]

/-- The level projections are locally constant (the digits up to level `n` determine the
level-`n` projection). -/
theorem isLocallyConstant_lvlOf (p n : ℕ) : IsLocallyConstant (lvlOf p n) := by
  intro s
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hcont : ∀ (i : Fin (p+1)) (k : Fin (n+1)),
      Continuous (fun y : ↥(cechTerm p) => digitsOf (y.1 i) (k : ℕ)) := by
    intro i k
    have h := (ConcreteCategory.hom (cechProj p i ≫ coord (k : ℕ))).continuous
    refine h.congr fun y => ?_
    simp only [ConcreteCategory.comp_apply, cechProj_hom, coord_hom]
    rfl
  have hcyl : IsOpen {y : ↥(cechTerm p) | ∀ (i : Fin (p+1)) (k : Fin (n+1)),
      digitsOf (y.1 i) (k : ℕ) = digitsOf (x.1 i) (k : ℕ)} := by
    have hrewrite : {y : ↥(cechTerm p) | ∀ (i : Fin (p+1)) (k : Fin (n+1)),
        digitsOf (y.1 i) (k : ℕ) = digitsOf (x.1 i) (k : ℕ)}
        = ⋂ (i : Fin (p+1)) (k : Fin (n+1)),
            (fun y : ↥(cechTerm p) => digitsOf (y.1 i) (k : ℕ)) ⁻¹'
              {digitsOf (x.1 i) (k : ℕ)} := by
      ext y; simp
    rw [hrewrite]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun k => ?_
    exact (hcont i k).isOpen_preimage _ (by
      have : DiscreteTopology ↥two := by
        show DiscreteTopology ↥(FintypeCat.of (Fin 2))
        exact FintypeCat.discreteTopology _
      exact isOpen_discrete _)
  have hsub : {y : ↥(cechTerm p) | ∀ (i : Fin (p+1)) (k : Fin (n+1)),
      digitsOf (y.1 i) (k : ℕ) = digitsOf (x.1 i) (k : ℕ)} ⊆ lvlOf p n ⁻¹' s := by
    intro y hy
    have hval : lvlOf p n y = lvlOf p n x := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      simp only [lvlOf_apply]
      exact truncVal_congr fun k hk => hy i ⟨k, by omega⟩
    rw [Set.mem_preimage, hval]
    exact hx
  exact Filter.mem_of_superset (hcyl.mem_nhds (by simp)) hsub


theorem lvlOf_compat' (p n : ℕ) (x y : ↥(cechTerm p)) (h : lvlOf p (n+1) x = lvlOf p (n+1) y) :
    lvlOf p n x = lvlOf p n y := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [← lvlOf_compat p n x i, ← lvlOf_compat p n y i, h]

theorem lvlOf_surjective (p n : ℕ) : Function.Surjective (lvlOf p n) := by
  intro y
  obtain ⟨Y, hYn, hcompat⟩ := exists_compat_extension p n y
  obtain ⟨x, hx⟩ := exists_cechTerm_of_compat p Y hcompat
    (fun d e h1 h2 => (ofDigitsTruncBound n d e).2 h1 h2)
  refine ⟨x, ?_⟩
  rw [← hYn]
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [lvlOf_apply]
  exact (hx n i).symm

/-- A locally constant `ℤ`-valued function on `cechTerm p` is constant on the fibres of some level
projection. -/
theorem exists_level_of_locallyConstant (p : ℕ) (f : ↥(cechTerm p) → ℤ)
    (hf : IsLocallyConstant f) :
    ∃ n : ℕ, ∀ x y : ↥(cechTerm p), lvlOf p n x = lvlOf p n y → f x = f y := by
  by_contra hcon
  push Not at hcon
  have hfiber : ∀ (n : ℕ) (w : Level.lev (2 ^ (n + 1)) p),
      IsOpen {x : ↥(cechTerm p) | lvlOf p n x = w} := fun n w => isLocallyConstant_lvlOf p n {w}
  have hfiber' : ∀ (n : ℕ) (w : Level.lev (2 ^ (n + 1)) p),
      IsOpen {x : ↥(cechTerm p) | lvlOf p n x ≠ w} := fun n w => isLocallyConstant_lvlOf p n {w}ᶜ
  have hffiber : ∀ a : ℤ, IsOpen {x : ↥(cechTerm p) | f x = a} := fun a => hf {a}
  have hffiber' : ∀ a : ℤ, IsOpen {x : ↥(cechTerm p) | f x ≠ a} := fun a => hf {a}ᶜ
  set K : ℕ → Set (↥(cechTerm p) × ↥(cechTerm p)) := fun n =>
    {q | lvlOf p n q.1 = lvlOf p n q.2 ∧ f q.1 ≠ f q.2} with hKdef
  have hanti : ∀ n, K (n + 1) ⊆ K n := by
    intro n q hq
    exact ⟨lvlOf_compat' p n q.1 q.2 hq.1, hq.2⟩
  have hne : ∀ n, (K n).Nonempty := by
    intro n
    obtain ⟨x, y, hxy, hfxy⟩ := hcon n
    exact ⟨(x, y), hxy, hfxy⟩
  have hclosed : ∀ n, IsClosed (K n) := by
    intro n
    have hE : IsClosed {q : ↥(cechTerm p) × ↥(cechTerm p) | lvlOf p n q.1 = lvlOf p n q.2} := by
      rw [← isOpen_compl_iff]
      have hset : {q : ↥(cechTerm p) × ↥(cechTerm p) | lvlOf p n q.1 = lvlOf p n q.2}ᶜ
          = ⋃ (w : Level.lev (2 ^ (n + 1)) p),
              ({x : ↥(cechTerm p) | lvlOf p n x = w} ×ˢ {x : ↥(cechTerm p) | lvlOf p n x ≠ w}) := by
        ext q
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
        constructor
        · intro hq
          exact ⟨lvlOf p n q.1, rfl, fun hc => hq hc.symm⟩
        · rintro ⟨w, h1, h2⟩ hc
          exact h2 (hc ▸ h1)
      rw [hset]
      exact isOpen_iUnion fun w => (hfiber n w).prod (hfiber' n w)
    have hD : IsClosed {q : ↥(cechTerm p) × ↥(cechTerm p) | f q.1 ≠ f q.2} := by
      rw [← isOpen_compl_iff]
      have hset : {q : ↥(cechTerm p) × ↥(cechTerm p) | f q.1 ≠ f q.2}ᶜ
          = ⋃ (a : ℤ), ({x : ↥(cechTerm p) | f x = a} ×ˢ {x : ↥(cechTerm p) | f x = a}) := by
        ext q
        simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq]
        constructor
        · intro hq
          exact ⟨f q.1, rfl, (not_not.mp hq).symm⟩
        · rintro ⟨a, h1, h2⟩ hc
          exact hc (by rw [h1, h2])
      rw [hset]
      exact isOpen_iUnion fun a => (hffiber a).prod (hffiber a)
    exact hE.inter hD
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
    hanti hne (hclosed 0).isCompact hclosed
  have hlev : ∀ n, lvlOf p n q.1 = lvlOf p n q.2 := fun n => (Set.mem_iInter.mp hq n).1
  have hneq : f q.1 ≠ f q.2 := (Set.mem_iInter.mp hq 0).2
  exact hneq (congrArg f (lvlOf_injective p hlev))

/-- Every locally constant `ℤ`-valued function on `cechTerm p` factors through a level
projection. -/
theorem exists_factor_lvlOf (p : ℕ) (f : ↥(cechTerm p) → ℤ) (hf : IsLocallyConstant f) :
    ∃ (n : ℕ) (F : Level.lev (2 ^ (n + 1)) p → ℤ), f = F ∘ lvlOf p n := by
  obtain ⟨n, hn⟩ := exists_level_of_locallyConstant p f hf
  refine ⟨n, fun w => f ((lvlOf_surjective p n w).choose), ?_⟩
  funext x
  have hspec := (lvlOf_surjective p n (lvlOf p n x)).choose_spec
  exact hn x _ hspec.symm


/-- **The level structure on the Čech nerve terms.**  There are level projections
`lvl n : cechTerm p → Level.lev (2^(n+1)) p` (truncation of every coordinate to `n+1` binary
digits) which are surjective, compatible with the division maps `v ↦ v/2`, jointly injective, and
such that every locally constant `ℤ`-valued function on `cechTerm p` factors through one of
them. -/
theorem cechTermLevelProjections (p : ℕ) :
    ∃ (lvl : ∀ n : ℕ, ↥(Work.ANALYTIC.CechPt.cechTerm p) →
        Work.ANALYTIC.CechPt.Level.lev (2^(n+1)) p),
      (∀ n : ℕ, Function.Surjective (lvl n)) ∧
      (∀ (n : ℕ) (x : ↥(Work.ANALYTIC.CechPt.cechTerm p)) (i : Fin (p+1)),
        (((lvl (n+1) x).1 i : ℕ) / 2 = ((lvl n x).1 i : ℕ))) ∧
      (∀ x y : ↥(Work.ANALYTIC.CechPt.cechTerm p), (∀ n, lvl n x = lvl n y) → x = y) ∧
      (∀ f : ↥(Work.ANALYTIC.CechPt.cechTerm p) → ℤ, IsLocallyConstant f →
        ∃ n : ℕ, ∃ F : Work.ANALYTIC.CechPt.Level.lev (2^(n+1)) p → ℤ, f = F ∘ lvl n) := by
  exact ⟨fun n => lvlOf p n, fun n => lvlOf_surjective p n, fun n x i => lvlOf_compat p n x i,
    fun x y h => lvlOf_injective p h, fun f hf => exists_factor_lvlOf p f hf⟩

end Work.ANALYTIC.CechPt
