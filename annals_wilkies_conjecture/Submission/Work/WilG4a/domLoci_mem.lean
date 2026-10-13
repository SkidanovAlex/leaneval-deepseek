/-
  WilG4a — the domination and sign loci are `Ω`-sets with a `D`-independent format.

  The statement `domLoci_mem` is the first step of the `n = 1` family lemma
  (`lipschitz_charts`): for an `Ω`-definable one-parameter family `f : ℝᵖ × ℝ → ℝ` the three
  loci

  * `domSet f g = {z | |∂_x f(z)| ≤ |∂_x g(z)|}`,
  * `posSet f = {z | ∂_x f(z) > 0}`,
  * `negSet f = {z | ∂_x f(z) < 0}`

  are `Ω`-definable with a format depending only on the input format `F0` and the parameter
  dimension `p`, and a degree which is a polynomial in the input degree `D`.

  ## The argument

  `derSet f ⊆ ℝ^{p+2}` is the set of pairs `(z,s)` such that `s` is the slice derivative of `f`
  at `z`; it is the `Sset` of `Work.WilG1.Plumb`, and `Sset_explicit` gives it format
  `AFR (p+1) F0 + 1` and degree `bDer p`.  Each of the three loci is then obtained from
  `derSet f`, `derSet g`, the half-spaces `{s > 0}`, `{s < 0}` and the comparison set
  `{|s| ≤ |t|}` by projections, intersections and coordinate pullbacks along the two
  inclusions `iotaA p, iotaB p : Fin (p+2) → Fin (p+3)` (all of these are in `lip_loci_defs`),
  so every constant in the answer is explicit.

  The only content beyond `Ω`-bookkeeping is the identification of the "auxiliary" sets with
  the loci themselves: `posSet = posSetAux`, `negSet = negSetAux` and `domSet = domSetAux`.
-/
import Mathlib
import Submission.Work.WilG4a.lip_loci_defs
import Submission.Work.WilG4a.Sset_explicit
import Submission.Work.WilG4a.sliceDiff_mem
import Submission.Work.WilG4a.domLociAlt
import Submission.Work.WilG4a.posSetAux_mem
import Submission.Work.WilG4a.negSetAux_mem
import Submission.Work.WilG4a.posSetAux_eq

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 1. The derivative set -/

-- (The one-variable degree polynomial produced by `Sset_explicit` for `derSet`.)
-- bDer: now imported from Submission.Work.WilG4a.domLociAlt (identical definition; dedup curric-46 10-12)

/-- `derSet f` is an `Ω`-set with the explicit bounds of `Sset_explicit`. -/
theorem derSet_mem {S : SOMin} {F0 D : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ}
    (hf : graphFam f ∈ S.Ω F0 D (p + 1 + 1)) :
    derSet f ∈ S.Ω (Work.WilG1.Plumb.AFR (p + 1) F0 + 1) ((bDer p).eval D) (p + 2) := by
  have h := Sset_explicit (S := S) (N := p + 1) (F := F0) (D := D) (f := famFun f)
    (Fin.last p) (by simpa using hf)
  simpa [derSet, bDer] using h

/-! ## 2. The domination and sign loci -/

/-- The sign loci are the projections of `derSet f` cut by the half-spaces.  This is the
`negSetAux = negSet` identification (`posSetAux_eq`, proved in a sibling module, is the
positive analogue). -/
theorem negSetAux_eq' (p : ℕ) (f : (Fin p → ℝ) → ℝ → ℝ) :
    negSetAux f = negSet f := by
  ext z
  simp only [negSetAux, negSet, WilkiesDesign.projLast, Set.mem_ofPred_eq, Set.mem_inter_iff,
    negHalf, Fin.snoc_last]
  constructor
  · rintro ⟨t, h1, h2⟩
    refine ⟨t, ?_, h2⟩
    rwa [mem_derSet, Fin.init_snoc, Fin.snoc_last] at h1
  · rintro ⟨s, hs, hspos⟩
    exact ⟨s, (mem_derSet f (Fin.snoc z s)).mpr (by simpa using hs), by simpa using hspos⟩

/-- The coordinate reindexing `(z,s,t) ↦ (z,s)` used in `domSetAux`. -/
theorem domSetAux_compA (p : ℕ) (z : Fin (p + 1) → ℝ) (t s : ℝ) :
    (Fin.snoc (Fin.snoc z t) s) ∘ iotaA p = Fin.snoc z t :=
  Fin.snoc_comp_castSucc

/-- The coordinate reindexing `(z,s,t) ↦ (z,t)` used in `domSetAux`.  The `let`-bound
`W, V` make the two `Fin.snoc`-blocks explicit as *functions* (as opposed to applications),
which the dependent type of `Fin.snoc` otherwise refuses to elaborate. -/
theorem domSetAux_compB (p : ℕ) (z : Fin (p + 1) → ℝ) (t s : ℝ) :
    (Fin.snoc (Fin.snoc z t) s) ∘ iotaB p = Fin.snoc z s := by
  let V : Fin (p + 2) → ℝ := Fin.snoc z s
  let W : Fin (p + 3) → ℝ := Fin.snoc (Fin.snoc z t) s
  change W ∘ iotaB p = V
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · show W (iotaB p (Fin.last (p + 1))) = V (Fin.last (p + 1))
    simp only [iotaB, Fin.lastCases_last, W, V, Fin.snoc_last]
  · show W (iotaB p (Fin.castSucc i)) = V (Fin.castSucc i)
    rw [iotaB, Fin.lastCases_castSucc]
    show (Fin.snoc (Fin.snoc z t) s : Fin (p + 3) → ℝ) (Fin.castAdd 2 i) =
      (Fin.snoc z s : Fin (p + 2) → ℝ) (Fin.castSucc i)
    rw [Fin.snoc_castSucc]
    rw [show Fin.castAdd 2 i = (Fin.castSucc (Fin.castSucc i) : Fin (p + 3)) from rfl]
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- `domSetAux f g` is the domination locus `domSet f g`. -/
theorem domSetAux_eq' (p : ℕ) (f g : (Fin p → ℝ) → ℝ → ℝ) :
    domSetAux f g = domSet f g := by
  ext z
  constructor
  · intro hz
    simp only [domSetAux, WilkiesDesign.projLast, Set.mem_ofPred_eq] at hz
    obtain ⟨t, s, hw⟩ := hz
    simp only [Set.mem_inter_iff, Work.WilG5.coordPre, Set.mem_ofPred_eq] at hw
    obtain ⟨⟨hA, hB⟩, hc⟩ := hw
    simp only [domSet, Set.mem_ofPred_eq]
    refine ⟨t, s, ?_, ?_, ?_⟩
    · rw [domSetAux_compA p z t s] at hA
      exact (mem_derSet_snoc p f z t).mp hA
    · rw [domSetAux_compB p z t s] at hB
      exact (mem_derSet_snoc p g z s).mp hB
    · simpa [cmpSet, Set.mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last] using hc
  · intro hz
    simp only [domSet, Set.mem_ofPred_eq] at hz
    obtain ⟨t, s, ht, hs, hc⟩ := hz
    simp only [domSetAux, WilkiesDesign.projLast, Set.mem_ofPred_eq]
    refine ⟨t, s, ?_⟩
    simp only [Set.mem_inter_iff, Work.WilG5.coordPre, Set.mem_ofPred_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [domSetAux_compA p z t s]
      exact (mem_derSet_snoc p f z t).mpr ht
    · rw [domSetAux_compB p z t s]
      exact (mem_derSet_snoc p g z s).mpr hs
    · simpa [cmpSet, Set.mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last] using hc

/-! ## 3. The `Ω`-membership of the three loci -/

theorem posSet_mem_aux (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) → posSetAux f ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨max (Work.WilG1.Plumb.AFR (p + 1) F0 + 1) (p + 4) + 2,
    bDer p + Polynomial.C 3, ?_⟩
  intro D f hf
  exact posSetAux_mem (S := S) (D := D) (f := f)
    (aS := Work.WilG1.Plumb.AFR (p + 1) F0 + 1) (bS := bDer p)
    (derSet_mem (S := S) (F0 := F0) (D := D) hf)

theorem negSet_mem_aux (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) → negSetAux f ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨max (Work.WilG1.Plumb.AFR (p + 1) F0 + 1) (p + 4) + 2,
    bDer p + Polynomial.C 3, ?_⟩
  intro D f hf
  exact negSetAux_mem (S := S) (D := D) (f := f)
    (aS := Work.WilG1.Plumb.AFR (p + 1) F0 + 1) (bS := bDer p)
    (derSet_mem (S := S) (F0 := F0) (D := D) hf)

/-- The format of the domination locus. -/
abbrev aDomLoci (p F0 : ℕ) : ℕ :=
  max (max ((Work.WilG1.Plumb.AFR (p + 1) F0 + 1) + 64 * ((p + 3) + (p + 2)) + 64)
           ((Work.WilG1.Plumb.AFR (p + 1) F0 + 1) + 64 * ((p + 3) + (p + 2)) + 64) + 1)
      (p + 6) + 1 + 1 + 1

/-- The degree polynomial of the domination locus. -/
abbrev bDomLoci (p : ℕ) : Polynomial ℕ :=
  ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)) +
    (bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32))) + Polynomial.C 4

theorem domSetAux_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) {f g : (Fin p → ℝ) → ℝ → ℝ},
      graphFam f ∈ S.Ω F0 D (p + 1 + 1) → graphFam g ∈ S.Ω F0 D (p + 1 + 1) →
      domSetAux f g ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨aDomLoci p F0, bDomLoci p, ?_⟩
  intro D f g hf hg
  have hdf := derSet_mem (S := S) (F0 := F0) (D := D) hf
  have hdg := derSet_mem (S := S) (F0 := F0) (D := D) hg
  have hA : Work.WilG5.coordPre (iotaA p) (derSet f) ∈
      S.Ω ((Work.WilG1.Plumb.AFR (p + 1) F0 + 1) + 64 * ((p + 3) + (p + 2)) + 64)
        ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)).eval D) (p + 3) :=
    Work.WilG1.Omega.mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 2) (N := p + 3) (ι := iotaA p)
        (A := derSet f) (F := Work.WilG1.Plumb.AFR (p + 1) F0 + 1)
        (D := (bDer p).eval D) hdf)
      le_rfl (le_of_eq (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega))
  have hB : Work.WilG5.coordPre (iotaB p) (derSet g) ∈
      S.Ω ((Work.WilG1.Plumb.AFR (p + 1) F0 + 1) + 64 * ((p + 3) + (p + 2)) + 64)
        ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)).eval D) (p + 3) :=
    Work.WilG1.Omega.mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 2) (N := p + 3) (ι := iotaB p)
        (A := derSet g) (F := Work.WilG1.Plumb.AFR (p + 1) F0 + 1)
        (D := (bDer p).eval D) hdg)
      le_rfl (le_of_eq (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega))
  have hcmp : cmpSet p ∈ S.Ω (p + 6) ((Polynomial.C 4).eval D) (p + 3) := cmpSet_mem S p D
  have h1 := Work.WilG1.Omega.inter₂ (S := S) hA hB
  have h2 := Work.WilG1.Omega.inter₂ (S := S) h1 hcmp
  have h3 := Work.WilG1.Omega.projLast_mem (S := S) (n := p + 2) h2
  have h4 := Work.WilG1.Omega.projLast_mem (S := S) (n := p + 1) h3
  exact h4

/-! ## 4. The theorem -/

theorem domLoci_mem (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f g : (Fin p → ℝ) → ℝ → ℝ},
        Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        Work.WilG4a.graphFam g ∈ S.Ω F0 D (p + 1 + 1) →
        Work.WilG4a.domSet f g ∈ S.Ω a (b.eval D) (p + 1) ∧
        Work.WilG4a.posSet f ∈ S.Ω a (b.eval D) (p + 1) ∧
        Work.WilG4a.negSet f ∈ S.Ω a (b.eval D) (p + 1) := by
  obtain ⟨ad, bd, hd⟩ := domSetAux_mem S p F0
  obtain ⟨ap, bp, hp⟩ := posSet_mem_aux S p F0
  obtain ⟨an, bn, hn⟩ := negSet_mem_aux S p F0
  refine ⟨max ad (max ap an), bd + bp + bn, ?_⟩
  intro D f g hf hg
  refine ⟨?_, ?_, ?_⟩
  · have h := hd D hf hg
    rw [domSetAux_eq' p f g] at h
    exact Work.WilG1.Omega.mono h (le_max_left _ _)
      (by simp only [Polynomial.eval_add]; omega)
  · have h := hp D hf
    rw [posSetAux_eq p f] at h
    exact Work.WilG1.Omega.mono h (le_trans (le_max_left ap an) (le_max_right _ _))
      (by simp only [Polynomial.eval_add]; omega)
  · have h := hn D hf
    rw [negSetAux_eq' p f] at h
    exact Work.WilG1.Omega.mono h (le_trans (le_max_right ap an) (le_max_right _ _))
      (by simp only [Polynomial.eval_add]; omega)

end Work.WilG4a
