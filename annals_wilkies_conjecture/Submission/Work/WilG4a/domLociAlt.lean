import Mathlib
import Submission.Work.WilG4a.lip_loci_defs
import Submission.Work.WilG4a.Sset_explicit
import Submission.Work.WilG4a.sliceDiff_mem

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}

/-! ## 0. The numerical bookkeeping -/

/-- The one-variable degree polynomial produced by `Sset_explicit` for `derSet`. -/
def bDer (p : ℕ) : Polynomial ℕ :=
  Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * Work.WilG1.Plumb.KK (p + 1) + (p + 1) * 4 + 80)

/-- The format of `derSet f` given by `Sset_explicit`. -/
def aDer (p F0 : ℕ) : ℕ := Work.WilG1.Plumb.AFR (p + 1) F0 + 1

/-- The format of the sign loci. -/
def aSign (p F0 : ℕ) : ℕ := max (aDer p F0) (p + 4) + 1 + 1

/-- The degree polynomial of the sign loci. -/
def bSign (p : ℕ) : Polynomial ℕ := bDer p + Polynomial.C 3

/-- The format of the domination locus. -/
def aDom (p F0 : ℕ) : ℕ :=
  max (max (aDer p F0 + 64 * ((p + 3) + (p + 2)) + 64)
           (aDer p F0 + 64 * ((p + 3) + (p + 2)) + 64) + 1) (p + 6) + 1 + 1 + 1

/-- The degree polynomial of the domination locus. -/
def bDom (p : ℕ) : Polynomial ℕ :=
  ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)) +
    (bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32))) + Polynomial.C 4

/-! ## 1. The derivative set -/

/-- `derSet f` is `Ω`-definable with the explicit bounds of `Sset_explicit`. -/
theorem derSet_memAlt (S : SOMin) (p F0 : ℕ) :
    ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
      derSet f ∈ S.Ω (aDer p F0) (Polynomial.eval D (bDer p)) (p + 2) := by
  intro D f hf
  have h := Sset_explicit (S := S) (N := p + 1) (F := F0) (D := D)
    (f := famFun f) (Fin.last p) (by simpa using hf)
  simpa [derSet, aDer, bDer] using h

/-! ## 2. The domination locus -/

/-- The reindexing `(z,s,t) ↦ (z,t)` written with `Fin.snoc`. -/
def iotaBs (p : ℕ) : Fin (p + 2) → Fin (p + 3) :=
  Fin.snoc (fun j : Fin (p + 1) => Fin.castSucc (Fin.castSucc j)) (Fin.last (p + 2))

/-- The domination locus written as the double projection of the set of `(z,s,t)` with
`(z,s) ∈ derSet f`, `(z,t) ∈ derSet g` and `|s| ≤ |t|`. -/
def domAux (f g : (Fin p → ℝ) → ℝ → ℝ) : Set (Fin (p + 1) → ℝ) :=
  projLast (projLast (Work.WilG5.coordPre (iotaA p) (derSet f) ∩
    Work.WilG5.coordPre (iotaBs p) (derSet g) ∩ cmpSet p))

theorem domAux_compA (z : Fin (p + 1) → ℝ) (s t : ℝ) :
    ((Fin.snoc (Fin.snoc z s) t : Fin (p + 3) → ℝ) ∘ iotaA p) = Fin.snoc z s := by
  have h : ((Fin.snoc (Fin.snoc z s) t : Fin (p + 3) → ℝ) ∘ iotaA p) =
      Fin.init (Fin.snoc (Fin.snoc z s) t : Fin (p + 3) → ℝ) := by
    funext i; rfl
  rw [h, Fin.init_snoc]

theorem domAux_compB (z : Fin (p + 1) → ℝ) (s t : ℝ) :
    ((Fin.snoc (Fin.snoc z s) t : Fin (p + 3) → ℝ) ∘ iotaBs p) = Fin.snoc z t := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl <;>
    simp [iotaBs, Function.comp_apply]

theorem domAux_eq (f g : (Fin p → ℝ) → ℝ → ℝ) : domAux f g = domSet f g := by
  ext z
  simp only [domAux, domSet, projLast, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Work.WilG5.coordPre, cmpSet]
  constructor
  · rintro ⟨u, v, ⟨hA, hB⟩, hC⟩
    rw [domAux_compA] at hA
    rw [domAux_compB] at hB
    rw [mem_derSet, Fin.init_snoc, Fin.snoc_last] at hA
    rw [mem_derSet, Fin.init_snoc, Fin.snoc_last] at hB
    have hC' : |u| ≤ |v| := by
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hC
    exact ⟨u, v, hA, hB, hC'⟩
  · rintro ⟨s, t, hs, ht, hle⟩
    refine ⟨s, t, ⟨?_, ?_⟩, ?_⟩
    · rw [domAux_compA, mem_derSet, Fin.init_snoc, Fin.snoc_last]; exact hs
    · rw [domAux_compB, mem_derSet, Fin.init_snoc, Fin.snoc_last]; exact ht
    · simpa only [cmpSet, Set.mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last] using hle

theorem domAux_mem (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f g : (Fin p → ℝ) → ℝ → ℝ},
        graphFam f ∈ S.Ω F0 D (p + 1 + 1) → graphFam g ∈ S.Ω F0 D (p + 1 + 1) →
        domAux f g ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨aDom p F0, bDom p, ?_⟩
  intro D f g hf hg
  have hA : Work.WilG5.coordPre (iotaA p) (derSet f) ∈
      S.Ω (aDer p F0 + 64 * ((p + 3) + (p + 2)) + 64)
        ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)).eval D) (p + 3) :=
    Work.WilG1.Omega.mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 2) (N := p + 3) (ι := iotaA p)
        (A := derSet f) (F := aDer p F0) (D := (bDer p).eval D) (derSet_memAlt S p F0 D hf))
      le_rfl (le_of_eq (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega))
  have hB : Work.WilG5.coordPre (iotaBs p) (derSet g) ∈
      S.Ω (aDer p F0 + 64 * ((p + 3) + (p + 2)) + 64)
        ((bDer p + Polynomial.C (32 * ((p + 3) + (p + 2)) + 32)).eval D) (p + 3) :=
    Work.WilG1.Omega.mono
      (Work.WilG5.coordPre_mem (S := S) (m := p + 2) (N := p + 3) (ι := iotaBs p)
        (A := derSet g) (F := aDer p F0) (D := (bDer p).eval D) (derSet_memAlt S p F0 D hg))
      le_rfl (le_of_eq (by simp only [Polynomial.eval_add, Polynomial.eval_C]; omega))
  have hcmp : cmpSet p ∈ S.Ω (p + 6) ((Polynomial.C 4).eval D) (p + 3) := cmpSet_mem S p D
  have h1 := Work.WilG1.Omega.inter₂ hA hB
  have h2 := Work.WilG1.Omega.inter₂ h1 hcmp
  have h3 := S.proj h2
  exact S.proj h3

/-! ## 3. The sign loci -/

theorem posSetAux_eq_alt (f : (Fin p → ℝ) → ℝ → ℝ) : posSetAux f = posSet f := by
  ext z
  simp only [posSetAux, posSet, projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, posHalf]
  constructor
  · rintro ⟨s, h1, h2⟩
    rw [mem_derSet, Fin.init_snoc, Fin.snoc_last] at h1
    exact ⟨s, h1, (by simpa using h2)⟩
  · rintro ⟨s, hs, hspos⟩
    exact ⟨s, (mem_derSet f (Fin.snoc z s)).mpr (by simpa using hs), by simpa using hspos⟩

theorem negSetAux_eq_alt (f : (Fin p → ℝ) → ℝ → ℝ) : negSetAux f = negSet f := by
  ext z
  simp only [negSetAux, negSet, projLast, Set.mem_ofPred_eq, Set.mem_inter_iff, negHalf]
  constructor
  · rintro ⟨s, h1, h2⟩
    rw [mem_derSet, Fin.init_snoc, Fin.snoc_last] at h1
    exact ⟨s, h1, (by simpa using h2)⟩
  · rintro ⟨s, hs, hspos⟩
    exact ⟨s, (mem_derSet f (Fin.snoc z s)).mpr (by simpa using hs), by simpa using hspos⟩

theorem posSetAux_memAlt (S : SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        posSetAux f ∈ S.Ω a (b.eval D) (p + 1) ∧ negSetAux f ∈ S.Ω a (b.eval D) (p + 1) := by
  refine ⟨aSign p F0, bSign p, ?_⟩
  intro D f hf
  have hD := derSet_memAlt S p F0 D hf
  have hp := posHalf_mem (S := S) (p + 2) (Fin.last (p + 1)) D
  have hn := negHalf_mem (S := S) (p + 2) (Fin.last (p + 1)) D
  constructor
  · have hi := Work.WilG1.Omega.inter₂ hD hp
    have hpr := S.proj hi
    refine Work.WilG1.Omega.mono hpr ?_ ?_
    · simp only [aSign]; omega
    · simp only [Polynomial.eval_add, Polynomial.eval_C, bSign]; omega
  · have hi := Work.WilG1.Omega.inter₂ hD hn
    have hpr := S.proj hi
    refine Work.WilG1.Omega.mono hpr ?_ ?_
    · simp only [aSign]; omega
    · simp only [Polynomial.eval_add, Polynomial.eval_C, bSign]; omega

/-! ## 4. The theorem -/

/-- **`Ω`-membership of `domSet`, `posSet`, `negSet`.** -/
theorem domLoci_memAlt (S : WilkiesDesign.SOMin) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (D : ℕ) {f g : (Fin p → ℝ) → ℝ → ℝ},
        graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        graphFam g ∈ S.Ω F0 D (p + 1 + 1) →
        domSet f g ∈ S.Ω a (b.eval D) (p + 1) ∧
        posSet f ∈ S.Ω a (b.eval D) (p + 1) ∧
        negSet f ∈ S.Ω a (b.eval D) (p + 1) := by
  obtain ⟨aS, bS, hS⟩ := posSetAux_memAlt S p F0
  obtain ⟨aD, bD, hD⟩ := domAux_mem S p F0
  refine ⟨max aD aS, bD + bS + bS, ?_⟩
  intro D f g hf hg
  refine ⟨?_, ?_, ?_⟩
  · rw [← domAux_eq f g]
    exact Work.WilG1.Omega.mono (hD D hf hg) (le_max_left _ _)
      (by simp only [Polynomial.eval_add]; omega)
  · rw [← posSetAux_eq_alt f]
    exact Work.WilG1.Omega.mono (hS D hf).1 (le_max_right _ _)
      (by simp only [Polynomial.eval_add]; omega)
  · rw [← negSetAux_eq_alt f]
    exact Work.WilG1.Omega.mono (hS D hf).2 (le_max_right _ _)
      (by simp only [Polynomial.eval_add]; omega)

end Work.WilG4a
