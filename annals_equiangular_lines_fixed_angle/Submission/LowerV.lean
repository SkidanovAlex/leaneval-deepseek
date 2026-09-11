import Submission.LowerD

open EquiangularLinesFixedAngle
open Filter
open Matrix
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option maxHeartbeats 1200000

/-! Stage 2 of the disjoint-union lower bound: explicit unit vectors.

The vertex type is `UType = (Fin c × Fin k0) ⊕ Fin t` (the copies and the isolates).
The ambient coordinate type is `WType = (Fin c × Fin (k0-1)) ⊕ (Fin t ⊕ Fin 1)`:
for each of the `c` copies we have a block of `k0-1` coordinates holding the per-copy
vectors `y`, then `t` isolated coordinates, then a shared last coordinate. -/

/-- Vertices: `c` copies of `k0` plus `t` isolates. -/
abbrev UType (k0 c t : ℕ) := (Fin c × Fin k0) ⊕ Fin t

/-- Ambient coordinates: copy-blocks, isolates, and the shared coordinate. -/
abbrev WType (k0 c t : ℕ) := (Fin c × Fin (k0 - 1)) ⊕ (Fin t ⊕ Fin 1)

/-- The coordinate function of the line for copy vertex `(s,i)`. -/
noncomputable def copyCoord {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (s : Fin c) (i : Fin k0) : WType k0 c t → ℝ :=
  fun z => match z with
    | Sum.inl (s', i') => if s' = s then Real.sqrt (1 - a) * ((y i) i') else 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr _) => Real.sqrt a

/-- The coordinate function of the line for isolate vertex `u`. -/
noncomputable def isoCoord {k0 c t : ℕ} (a : ℝ) (u : Fin t) : WType k0 c t → ℝ :=
  fun z => match z with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl u') => if u' = u then Real.sqrt (1 - a) else 0
    | Sum.inr (Sum.inr _) => Real.sqrt a

/-- Put coordinate functions into the ambient Euclidean space of the right dimension. -/
noncomputable def wToEuc {k0 c t : ℕ} (f : WType k0 c t → ℝ) : Euc (Fintype.card (WType k0 c t)) :=
  eucOfFun (fun j : Fin (Fintype.card (WType k0 c t)) => f ((Fintype.equivFin (WType k0 c t)).symm j))

/-- The family of lines indexed by `UType`. -/
noncomputable def linesFamily {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ) :
    UType k0 c t → Euc (Fintype.card (WType k0 c t)) :=
  fun v => match v with
    | Sum.inl (s, i) => wToEuc (copyCoord (k0 := k0) (c := c) (t := t) y a s i)
    | Sum.inr u => wToEuc (isoCoord (k0 := k0) (c := c) (t := t) a u)

/-- Main coordinate part of a `WType` function. -/
def wMain {k0 c t : ℕ} (f : WType k0 c t → ℝ) : (Fin c × Fin (k0 - 1)) → ℝ :=
  fun p => f (Sum.inl p)

/-- Tail (isolates + shared) coordinate part. -/
def wTail {k0 c t : ℕ} (f : WType k0 c t → ℝ) : (Fin t ⊕ Fin 1) → ℝ :=
  fun q => f (Sum.inr q)

/-- isolate coordinates. -/
def wIso {k0 c t : ℕ} (f : WType k0 c t → ℝ) : Fin t → ℝ :=
  fun u => f (Sum.inr (Sum.inl u))

/-- the shared coordinate. -/
def wOne {k0 c t : ℕ} (f : WType k0 c t → ℝ) : Fin 1 → ℝ :=
  fun u => f (Sum.inr (Sum.inr u))

/-- dot product over a sum type splits. -/
lemma dotProduct_sum_sum {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (f g : ι₁ ⊕ ι₂ → ℝ) : f ⬝ᵥ g
      = (f ∘ Sum.inl) ⬝ᵥ (g ∘ Sum.inl) + (f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr) := by
  classical
  simp [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib, Function.comp_def]

/-- inner product over `WType` splits into the three parts. -/
lemma wDot_split {k0 c t : ℕ} (f g : WType k0 c t → ℝ) :
    f ⬝ᵥ g = (wMain f ⬝ᵥ wMain g) + (wIso f ⬝ᵥ wIso g) + (wOne f ⬝ᵥ wOne g) := by
  classical
  have h1 : f ⬝ᵥ g = (wMain f ⬝ᵥ wMain g) + ((f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr)) := by
    rw [dotProduct_sum_sum]
    rfl
  have h2 : ((f ∘ Sum.inr) ⬝ᵥ (g ∘ Sum.inr))
      = (wIso f ⬝ᵥ wIso g) + (wOne f ⬝ᵥ wOne g) := by
    rw [dotProduct_sum_sum]
    rfl
  rw [h1, h2]
  ring

/-- inner product over the copy-block splits as a sum over copies of sums. -/
lemma wMain_split {k0 c : ℕ} (f g : (Fin c × Fin (k0 - 1)) → ℝ) :
    f ⬝ᵥ g = ∑ s : Fin c, ∑ i' : Fin (k0 - 1), f (s, i') * g (s, i') := by
  classical
  simp [dotProduct, Fintype.sum_prod_type]

/-- dot product over `Fin 1` is the single value. -/
lemma dotProduct_fin_one (f g : Fin 1 → ℝ) : f ⬝ᵥ g = f 0 * g 0 := by
  classical
  simp [dotProduct]

/-- dot product over `Fin n` for `n = 0` is zero. -/
lemma dotProduct_fin_zero {n : ℕ} (h : n = 0) (f g : Fin n → ℝ) : f ⬝ᵥ g = 0 := by
  classical
  subst n
  simp [dotProduct]

/-- dot products with the zero function vanish. -/
lemma dotProduct_zero_fun_left {ι : Type*} [Fintype ι] (g : ι → ℝ) : (0 : ι → ℝ) ⬝ᵥ g = 0 := by
  simp [dotProduct]
lemma dotProduct_zero_fun_right {ι : Type*} [Fintype ι] (f : ι → ℝ) : f ⬝ᵥ (0 : ι → ℝ) = 0 := by
  simp [dotProduct]

/-- The shared coordinate of a copy line is `√a`. -/
lemma wOne_copy_val {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (s : Fin c) (i : Fin k0) : ∀ z : Fin 1, wOne (copyCoord (k0 := k0) (c := c) (t := t) y a s i) z = Real.sqrt a := by
  intro z
  fin_cases z
  simp [wOne, copyCoord]

/-- The shared coordinate of an isolate line is `√a`. -/
lemma wOne_iso_val {k0 c t : ℕ} (a : ℝ) (u : Fin t) : ∀ z : Fin 1, wOne (isoCoord (k0 := k0) (c := c) (t := t) a u) z = Real.sqrt a := by
  intro z
  fin_cases z
  simp [wOne, isoCoord]

/-- The isolate coordinates of a copy line vanish. -/
lemma wIso_copy_zero {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (s : Fin c) (i : Fin k0) : ∀ u : Fin t, wIso (copyCoord (k0 := k0) (c := c) (t := t) y a s i) u = 0 := by
  intro u
  simp [wIso, copyCoord]

/-- The copy coordinates of an isolate line vanish. -/
lemma wMain_iso_zero {k0 c t : ℕ} (a : ℝ) (u : Fin t) :
    ∀ p : Fin c × Fin (k0 - 1), wMain (isoCoord (k0 := k0) (c := c) (t := t) a u) p = 0 := by
  intro p
  cases p with
  | mk s i => simp [wMain, isoCoord]

/-- The shared part of two lines with shared coordinate `√a` contributes `a`. -/
lemma wOne_lines {k0 c t : ℕ} (f g : WType k0 c t → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hf : ∀ z : Fin 1, wOne f z = Real.sqrt a) (hg : ∀ z : Fin 1, wOne g z = Real.sqrt a) :
    wOne f ⬝ᵥ wOne g = a := by
  rw [dotProduct_fin_one, hf 0, hg 0]
  rw [← sq, Real.sq_sqrt ha]

/-- dot product is invariant under reindexing coordinates. -/
lemma dotProduct_reindex {ι : Type*} [Fintype ι] [DecidableEq ι] (f g : ι → ℝ) :
    (fun j : Fin (Fintype.card ι) => f ((Fintype.equivFin ι).symm j)) ⬝ᵥ
      (fun j : Fin (Fintype.card ι) => g ((Fintype.equivFin ι).symm j)) = f ⬝ᵥ g := by
  classical
  simp [dotProduct]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm
    (fun j : Fin (Fintype.card ι) => f ((Fintype.equivFin ι).symm j) * g ((Fintype.equivFin ι).symm j))
    (fun b : ι => f b * g b) (by intro x; rfl)

/-- inner product in the reindexed ambient space equals the coordinate dot product. -/
lemma inner_wToEuc {k0 c t : ℕ} (f g : WType k0 c t → ℝ) :
    ⟪wToEuc (k0 := k0) (c := c) (t := t) f, wToEuc (k0 := k0) (c := c) (t := t) g⟫ = f ⬝ᵥ g := by
  classical
  unfold wToEuc
  rw [← dotProduct_eq_inner]
  rw [dotProduct_reindex]

open Classical in
/-- The entries of the per-copy Gram matrix. -/
lemma perCopyGram_apply (lam : ℝ) {k0 : ℕ} (H : SimpleGraph (Fin k0)) (hlamz : lam ≠ 0)
    (i j : Fin k0) :
    perCopyGram lam H i j = (if i = j then 1 else if H.Adj i j then - (1 / lam) else 0) := by
  classical
  calc
    perCopyGram lam H i j = (1 / lam) * (((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ)) i j) := by
      simp [perCopyGram, smul_eq_mul]
    _ = (if i = j then 1 else if H.Adj i j then - (1 / lam) else 0) := by
      by_cases hij : i = j
      · subst j
        have hloop : ¬ H.Adj i i := H.loopless.irrefl i
        have hzii : (((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ)) i i) = lam := by
          simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, SimpleGraph.adjMatrix_apply, hloop]
        rw [hzii]
        simp [hlamz]
      · by_cases hadj : H.Adj i j
        · have hval : (((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ)) i j) = -1 := by
            simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, hij, hadj, SimpleGraph.adjMatrix_apply]
          rw [hval]
          simp [hij, hadj]
        · have hval : (((lam • (1 : Matrix (Fin k0) (Fin k0) ℝ)) - (H.adjMatrix ℝ)) i j) = 0 := by
            simp [Matrix.sub_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, hij, hadj, SimpleGraph.adjMatrix_apply]
          rw [hval]
          simp [hij, hadj]

/-- inner product between two copy-lines: the copy part. -/
lemma copyMain_dot {k0 c t : ℕ} (y : Fin k0 → Euc (k0 - 1)) (a : ℝ)
    (ha : 0 ≤ 1 - a) (s s' : Fin c) (i j : Fin k0) :
    (wMain (copyCoord (k0 := k0) (c := c) (t := t) y a s i))
        ⬝ᵥ (wMain (copyCoord (k0 := k0) (c := c) (t := t) y a s' j))
      = (if s = s' then (1 - a) * ⟪y i, y j⟫ else 0) := by
  classical
  have hsq : Real.sqrt (1 - a) * Real.sqrt (1 - a) = 1 - a := by
    rw [← sq, Real.sq_sqrt ha]
  rw [wMain_split]
  calc
    (∑ s'' : Fin c, ∑ i'' : Fin (k0 - 1),
        (if s'' = s then Real.sqrt (1 - a) * (y i) i'' else 0)
          * (if s'' = s' then Real.sqrt (1 - a) * (y j) i'' else 0))
        = (∑ s'' : Fin c, (if s'' = s ∧ s'' = s' then
              (1 - a) * (∑ i'' : Fin (k0 - 1), (y i) i'' * (y j) i'') else 0)) := by
          apply Finset.sum_congr rfl
          intro s'' hs''
          by_cases h1 : s'' = s
          · subst s''
            by_cases h2 : s = s'
            · subst s'
              simp
              change (∑ x ∈ (Finset.univ : Finset (Fin (k0 - 1))),
                  Real.sqrt (1 - a) * (y i) x * (Real.sqrt (1 - a) * (y j) x))
                  = (1 - a) * (∑ x ∈ (Finset.univ : Finset (Fin (k0 - 1))), (y i) x * (y j) x)
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x hx
              calc
                Real.sqrt (1 - a) * (y i) x * (Real.sqrt (1 - a) * (y j) x)
                    = (Real.sqrt (1 - a) * Real.sqrt (1 - a)) * ((y i) x * (y j) x) := by ring
                _ = (1 - a) * ((y i) x * (y j) x) := by rw [hsq]
            · simp [h2]
          · simp [h1]
    _ = (if s = s' then (1 - a) * (∑ i'' : Fin (k0 - 1), (y i) i'' * (y j) i'') else 0) := by
          by_cases hss' : s = s'
          · subst s'
            simp
          · have hsum : (∑ s'' : Fin c, if s'' = s ∧ s'' = s' then
                (1 - a) * (∑ i'' : Fin (k0 - 1), (y i) i'' * (y j) i'') else 0) = 0 := by
              apply Finset.sum_eq_zero
              intro s'' hs''
              have hnot : ¬ (s'' = s ∧ s'' = s') := by
                intro h
                exact hss' (h.1.symm.trans h.2)
              simp [hnot]
            simpa [hss'] using hsum
    _ = (if s = s' then (1 - a) * ⟪y i, y j⟫ else 0) := by
          rw [euclidean_inner_apply]

/-- isolate coordinates: the dot of two isolate lines. -/
lemma wIso_iso_dot {k0 c t : ℕ} (a : ℝ) (ha : 0 ≤ 1 - a) (u u' : Fin t) :
    wIso (isoCoord (k0 := k0) (c := c) (t := t) a u) ⬝ᵥ
      wIso (isoCoord (k0 := k0) (c := c) (t := t) a u') = (if u = u' then 1 - a else 0) := by
  classical
  have hsq : Real.sqrt (1 - a) * Real.sqrt (1 - a) = 1 - a := by
    rw [← sq, Real.sq_sqrt ha]
  simp only [dotProduct, wIso, isoCoord]
  by_cases h : u = u'
  · subst u'
    have h1 : (∑ u'' : Fin t, (if u'' = u then Real.sqrt (1 - a) else 0) * (if u'' = u then Real.sqrt (1 - a) else 0)) = 1 - a := by
      calc
        (∑ u'' : Fin t, (if u'' = u then Real.sqrt (1 - a) else 0) * (if u'' = u then Real.sqrt (1 - a) else 0))
            = ∑ u'' : Fin t, (if u'' = u then (1 - a) else 0) := by
              apply Finset.sum_congr rfl
              intro u'' hu''
              by_cases h1u : u'' = u
              · subst u''
                simp [hsq]
              · simp [h1u]
        _ = 1 - a := by
              have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin t)))
                (f := fun u'' : Fin t => if u'' = u then (1 - a) else 0) u
                (by intro b hb hne; simp [hne]) (by intro hm; exfalso; exact hm (Finset.mem_univ u))
              simpa using h
    rw [h1]
    simp
  · have hsum : (∑ u'' : Fin t, (if u'' = u then Real.sqrt (1 - a) else 0) * (if u'' = u' then Real.sqrt (1 - a) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro u'' hu''
      by_cases h1 : u'' = u <;> by_cases h2 : u'' = u'
      · exfalso
        exact h (h1.symm.trans h2)
      · subst u''
        simp [h2]
      · subst u''
        simp [h1]
      · simp [h1, h2]
    simpa [h] using hsum

end Submission
