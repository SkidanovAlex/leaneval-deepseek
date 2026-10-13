/-
  WilC4 / cdbPieces : `paramBnd_slice`.

  If `S ⊆ ℝ^{n+1}` is `∅`-definable in `LRc`, then so is the set of parameters `p` for which
  `p 0` is a boundary point (`Work.WilC2.IsBnd`) of the fibre
  `Pfib1 S p = {x | Fin.cons x (Fin.tail p) ∈ S}`.

  This parametrises `Work.WilC2.bnd_definable_alt`: the topological boundary of a set `D` is the
  complement of `InteriorSet D ∪ InteriorSet Dᶜ`, and the *parametric* interior
  `p ↦ InteriorSet (Pfib1 S p)` is definable by the same first-order transcription as
  `Work.WilC2.definable_interior`, with the single point variable of the fibre replaced by the
  whole parameter tuple.

  The index bookkeeping: a "quadruple" carries `(p, a, b, z)` with `p` on `Fin (n+1)`, the two
  interval endpoints `a`, `b` on `Fin 2` and the point `z` on `Fin 1`; the relevant fibre
  coordinate is `Fin.cons z (Fin.tail p)`, obtained by pulling `S` back along `pSliceτ n`.
-/
import Mathlib
import Submission.Work.WilC4.ParamMonoDefs
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.bnd_definable_alt

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4.cdbPieces

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index map reindexing `(z, p₁, …, pₙ)` into the quadruple -/

/-- The index type of the quadruples `(p, a, b, z)`: the parameter tuple `p` on `Fin (n+1)`,
the two endpoints `a`, `b` of an interval on `Fin 2`, and the interior point `z` on `Fin 1`. -/
abbrev QIdx (n : ℕ) : Type := (Fin (n + 1) ⊕ Fin 2) ⊕ Fin 1

/-- The index type of the triples `(p, a, b)`. -/
abbrev TIdx (n : ℕ) : Type := Fin (n + 1) ⊕ Fin 2

/-- The map reindexing the tuple `(z, p₁, …, pₙ)` (a fibre point `z` followed by the parameter
tuple `p`) as a tuple on `QIdx n`: the coordinate `0` is `z : Fin 1`, the coordinate `i+1` is the
`i+1`-st component of `p`. -/
def pSliceτ (n : ℕ) : Fin (n + 1) → QIdx n :=
  Fin.cons (Sum.inr (0 : Fin 1)) (fun j : Fin n => Sum.inl (Sum.inl (Fin.succ j)))

/-- Pulling a function on `QIdx n` back along `pSliceτ` yields the tuple
`Fin.cons (w (inr 0)) (Fin.tail p)`. -/
lemma pSliceτ_comp {n : ℕ} (w : QIdx n → ℝ) :
    w ∘ pSliceτ n =
      Fin.cons (w (Sum.inr (0 : Fin 1)))
        (Fin.tail (fun i : Fin (n + 1) => w (Sum.inl (Sum.inl i)))) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j => rfl

/-! ## 2. The parametric interior -/

/-- `p ∈ PInt S` iff `p 0` is an interior point of the fibre `Pfib1 S p` (in the sense of
`Work.WilC2.InteriorSet`). -/
def PInt {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) : Set (Fin (n + 1) → ℝ) :=
  {p | p 0 ∈ Work.WilC2.InteriorSet (Pfib1 S p)}

/-- Every nonnegative real is a square. -/
private lemma sq_real : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z :=
  fun x hx => ⟨Real.sqrt x, by rw [← pow_two, Real.sq_sqrt hx]⟩

/-- The fibre of the complement family is the complement of the fibre. -/
@[simp] lemma Pfib1_compl {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) (p : Fin (n + 1) → ℝ) :
    Pfib1 Sᶜ p = (Pfib1 S p)ᶜ := by
  ext z
  simp [Pfib1]

/-- The quadruple relation underlying the parametric interior: `(p, a, b, z)` with `a < z < b`
and `z` outside the fibre `Pfib1 S p`. -/
def PIntBad {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) : Set (QIdx n → ℝ) :=
  {w | w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr (1 : Fin 2))) ∧
       w (Sum.inl (Sum.inr (0 : Fin 2))) < w (Sum.inr (0 : Fin 1)) ∧
       Fin.cons (w (Sum.inr (0 : Fin 1)))
         (Fin.tail (fun i : Fin (n + 1) => w (Sum.inl (Sum.inl i)))) ∈ Sᶜ}

/-- `PIntBad` is the intersection of the three elementary pieces below. -/
def PIntBadA (n : ℕ) : Set (QIdx n → ℝ) :=
  {w | w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr (1 : Fin 2)))}

/-- See `PIntBad`. -/
def PIntBadB (n : ℕ) : Set (QIdx n → ℝ) :=
  {w | w (Sum.inl (Sum.inr (0 : Fin 2))) < w (Sum.inr (0 : Fin 1))}

/-- See `PIntBad`. -/
def PIntBadC {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) : Set (QIdx n → ℝ) :=
  (fun w : QIdx n → ℝ => w ∘ pSliceτ n) ⁻¹' Sᶜ

lemma PIntBad_eq {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) :
    PIntBad S = (PIntBadA n ∩ PIntBadB n) ∩ PIntBadC S := by
  ext w
  simp only [PIntBad, PIntBadA, PIntBadB, PIntBadC, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_preimage, Set.mem_compl_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, by rw [pSliceτ_comp (n := n) w]; exact h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, by rw [pSliceτ_comp (n := n) w] at h3; exact h3⟩

/-- The triple relation: `(p, a, b)` such that no `z ∈ (a, b)` witnesses that the fibre misses
`(a, b)`. -/
def PIntTriple {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) : Set (TIdx n → ℝ) :=
  {v | v (Sum.inr (0 : Fin 2)) < v (Sum.inl (0 : Fin (n + 1))) ∧
       v (Sum.inl (0 : Fin (n + 1))) < v (Sum.inr (1 : Fin 2)) ∧
       ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ (PIntBad S)ᶜ}

/-- See `PIntTriple`. -/
def PIntTripleA (n : ℕ) : Set (TIdx n → ℝ) :=
  {v | v (Sum.inr (0 : Fin 2)) < v (Sum.inl (0 : Fin (n + 1)))}

/-- See `PIntTriple`. -/
def PIntTripleB (n : ℕ) : Set (TIdx n → ℝ) :=
  {v | v (Sum.inl (0 : Fin (n + 1))) < v (Sum.inr (1 : Fin 2))}

/-- See `PIntTriple`. -/
def PIntTripleC {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) : Set (TIdx n → ℝ) :=
  {v | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ (PIntBad S)ᶜ}

lemma PIntTriple_eq {n : ℕ} (S : Set (Fin (n + 1) → ℝ)) :
    PIntTriple S = (PIntTripleA n ∩ PIntTripleB n) ∩ PIntTripleC S := by
  ext v
  simp only [PIntTriple, PIntTripleA, PIntTripleB, PIntTripleC, Set.mem_inter_iff,
    Set.mem_setOf_eq]
  tauto

/-! ### 2.1 Definability of the two auxiliary relations -/

lemma PIntBad_definable {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (PIntBad S) := by
  have hA : (∅ : Set ℝ).Definable LRc (PIntBadA n) := by
    unfold PIntBadA
    exact WilC2.definable_lt (M := ℝ) (A := (∅ : Set ℝ)) (α := QIdx n) sq_real _ _
  have hB : (∅ : Set ℝ).Definable LRc (PIntBadB n) := by
    unfold PIntBadB
    exact WilC2.definable_lt (M := ℝ) (A := (∅ : Set ℝ)) (α := QIdx n) sq_real _ _
  have hC : (∅ : Set ℝ).Definable LRc (PIntBadC S) := hS.compl.preimage_comp (pSliceτ n)
  have h := (hA.inter hB).inter hC
  rwa [← PIntBad_eq S] at h

lemma PIntTriple_definable {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (PIntTriple S) := by
  have ha : (∅ : Set ℝ).Definable LRc (PIntTripleA n) := by
    unfold PIntTripleA
    exact WilC2.definable_lt (M := ℝ) (A := (∅ : Set ℝ)) (α := TIdx n) sq_real _ _
  have hb : (∅ : Set ℝ).Definable LRc (PIntTripleB n) := by
    unfold PIntTripleB
    exact WilC2.definable_lt (M := ℝ) (A := (∅ : Set ℝ)) (α := TIdx n) sq_real _ _
  have hc : (∅ : Set ℝ).Definable LRc (PIntTripleC S) := by
    unfold PIntTripleC
    exact (PIntBad_definable hS).compl.forall_of_finite (α := TIdx n) (β := Fin 1)
  have h := (ha.inter hb).inter hc
  rwa [← PIntTriple_eq S] at h

/-! ### 2.2 Pointwise descriptions -/

/-- Membership in `PIntBad` in coordinates. -/
lemma mem_PIntBad_iff {n : ℕ} {S : Set (Fin (n + 1) → ℝ)} (p : Fin (n + 1) → ℝ)
    (a b : ℝ) (u : Fin 1 → ℝ) :
    Sum.elim (Sum.elim p ![a, b]) u ∈ PIntBad S ↔
      (u 0 < b ∧ a < u 0 ∧ Fin.cons (u 0) (Fin.tail p) ∈ Sᶜ) := by
  simp only [PIntBad, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩

/-- The `∀ z` clause of the parametric interior, in the indexed form produced by
`Definable.forall_of_finite`. -/
lemma forall_elim_PIntBad_iff {n : ℕ} {S : Set (Fin (n + 1) → ℝ)} (p : Fin (n + 1) → ℝ)
    (a b : ℝ) :
    (∀ u : Fin 1 → ℝ, Sum.elim (Sum.elim p ![a, b]) u ∈ (PIntBad S)ᶜ) ↔
      ∀ z : ℝ, a < z → z < b → Fin.cons z (Fin.tail p) ∈ S := by
  constructor
  · intro h z haz hzb
    by_contra hz
    have hmem : Sum.elim (Sum.elim p ![a, b]) (fun _ : Fin 1 => z) ∈ PIntBad S := by
      rw [mem_PIntBad_iff]
      exact ⟨hzb, haz, hz⟩
    exact (h (fun _ : Fin 1 => z)) hmem
  · intro h u hcontra
    rw [mem_PIntBad_iff] at hcontra
    obtain ⟨h1, h2, h3⟩ := hcontra
    exact h3 (h (u 0) h2 h1)

/-- Membership in `PIntTriple` in coordinates. -/
lemma mem_PIntTriple_iff {n : ℕ} {S : Set (Fin (n + 1) → ℝ)} {p : Fin (n + 1) → ℝ}
    {a b : ℝ} :
    Sum.elim p ![a, b] ∈ PIntTriple S ↔
      a < p 0 ∧ p 0 < b ∧ ∀ z : ℝ, a < z → z < b → Fin.cons z (Fin.tail p) ∈ S := by
  rw [PIntTriple]
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using h1, by simpa using h2, (forall_elim_PIntBad_iff p a b).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by simpa using h1, by simpa using h2, (forall_elim_PIntBad_iff p a b).mpr h3⟩

/-! ### 2.3 The parametric interior is definable -/

theorem paramInt_definable {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable LRc S) :
    (∅ : Set ℝ).Definable LRc (PInt S) := by
  have htriple := PIntTriple_definable hS
  have hproj := htriple.exists_of_finite (α := Fin (n + 1)) (β := Fin 2)
  have hset : {p : Fin (n + 1) → ℝ | ∃ u : Fin 2 → ℝ, Sum.elim p u ∈ PIntTriple S} = PInt S := by
    ext p
    constructor
    · rintro ⟨u, hu⟩
      have hu' : Sum.elim p ![u 0, u 1] ∈ PIntTriple S := by
        rwa [show u = ![u 0, u 1] from funext fun k => by fin_cases k <;> rfl] at hu
      obtain ⟨h1, h2, h3⟩ := (mem_PIntTriple_iff (p := p) (a := u 0) (b := u 1)).mp hu'
      exact ⟨u 0, u 1, h1, h2, fun z hz => h3 z hz.1 hz.2⟩
    · rintro ⟨a, b, ha, hb, hsub⟩
      refine ⟨![a, b], ?_⟩
      rw [mem_PIntTriple_iff]
      exact ⟨ha, hb, fun z hz1 hz2 => hsub ⟨hz1, hz2⟩⟩
  rw [hset] at hproj
  exact hproj

/-! ## 3. The boundary set of the fibre family -/

/-- **The boundary set of the fibre family is definable.**  The boundary points of a set `D` are
exactly the points lying in neither `InteriorSet D` nor `InteriorSet Dᶜ`, so the parametric
boundary set is the complement of `PInt S ∪ PInt Sᶜ`; both parts are definable by
`paramInt_definable`. -/
theorem paramBnd_slice {n : ℕ} {S : Set (Fin (n + 1) → ℝ)}
    (hS : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc S) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      {p : Fin (n + 1) → ℝ | Work.WilC2.IsBnd (Work.WilC4.Pfib1 S p) (p 0)} := by
  have h1 : (∅ : Set ℝ).Definable LRc (PInt S) := paramInt_definable hS
  have h2 : (∅ : Set ℝ).Definable LRc (PInt Sᶜ) := paramInt_definable hS.compl
  have hgoal : (PInt S ∪ PInt Sᶜ)ᶜ = {p : Fin (n + 1) → ℝ |
      Work.WilC2.IsBnd (Work.WilC4.Pfib1 S p) (p 0)} := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_setOf_eq, PInt,
      Pfib1_compl, Work.WilC2.IsBnd]
    constructor
    · rintro ⟨hA, hB⟩
      exact ⟨fun h => hA ((Work.WilC2.exists_Ioo_subset_iff_interior (M := ℝ)
          (D := Work.WilC4.Pfib1 S p) (x := p 0)).mp h),
        fun h => hB ((Work.WilC2.exists_Ioo_subset_iff_interior (M := ℝ)
          (D := (Work.WilC4.Pfib1 S p)ᶜ) (x := p 0)).mp h)⟩
    · rintro ⟨hA, hB⟩
      exact ⟨fun h => hA ((Work.WilC2.exists_Ioo_subset_iff_interior (M := ℝ)
          (D := Work.WilC4.Pfib1 S p) (x := p 0)).mpr h),
        fun h => hB ((Work.WilC2.exists_Ioo_subset_iff_interior (M := ℝ)
          (D := (Work.WilC4.Pfib1 S p)ᶜ) (x := p 0)).mpr h)⟩
  have h3 : (∅ : Set ℝ).Definable LRc (PInt S ∪ PInt Sᶜ)ᶜ := (h1.union h2).compl
  rwa [hgoal] at h3

end Work.WilC4.cdbPieces
