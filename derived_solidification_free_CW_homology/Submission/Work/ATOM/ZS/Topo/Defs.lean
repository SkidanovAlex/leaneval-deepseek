import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.ZS.Data

/-!
# AREA ATOM / `ℤ[S]`: the explicit maps of `NOTES_LEAD_solid_gaps1.md` §3.1

This file defines the *underlying functions* of the continuous maps used to build the null sequence
of REFS/03 §1, together with their elementary pointwise values.  The maps are

* `ePred`  — `ẽ : (ℕ∪{∞}) × S ⟶ S`, `(0,x) ↦ s₀`, `(k+1,x) ↦ e_k x`, `(∞,x) ↦ x`;
* `betaFun`— `β : (ℕ∪{∞}) × S ⟶ S`, `(j,x) ↦ e_{n(j)-1} x` (`s₀` when `n(j) = 0`), `(∞,x) ↦ x`;
* `psiFun` — `ψ : (ℕ∪{∞}) × S ⟶ ℕ∪{∞}`, `(k,x) ↦ idx (e_k x)` if `e_k x = a_j` with `n(j) = k`
  and `e_k x ≠ s₀`, and `∞` otherwise;
* `phiPFun` — `φ_P : (ℕ∪{∞}) × (ℕ∪{∞}) ⟶ ℕ∪{∞}`, `(k,j) ↦ j` if `k ≤ n(j)`, and `∞` otherwise;
* `tSet`  — the closed subset `T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S` of `(ℕ∪{∞}) × S`.

Continuity of these functions is proved separately (`Submission/Work/ATOM/ZS/Topo/EPredCont.lean`
and friends); this file only contains the pointwise combinatorics, so that the statements of the
continuity lemmas can refer to a fixed, canonical underlying function.

The one topological tool recorded here (and used by the continuity proofs) is the criterion
`continuous_onePoint_iff_isClopen`: a map into `ℕ∪{∞}` is continuous exactly when all its fibres
over finite points are clopen.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

/-- `(ℕ∪{∞}) ⊗ S`, the source of `ẽ`, `β` and `ψ`. -/
abbrev NS (S : LightProfinite.{0}) : LightProfinite.{0} := (ℕ∪{∞}) ⊗ S

/-- `(ℕ∪{∞}) ⊗ (ℕ∪{∞})`, the source of `φ_P`. -/
abbrev NS2 : LightProfinite.{0} := (ℕ∪{∞}) ⊗ (ℕ∪{∞})

/-- The point `(k,x)` of `(ℕ∪{∞}) ⊗ S`.  (The product of light profinite sets is the
type-theoretic product, but the elaborator does not always see it; this abbreviation makes it
explicit.) -/
abbrev mkNS (S : LightProfinite.{0}) (k : LightProfinite.NatUnionInfty) (x : ↥S) : ↥(NS S) :=
  (k, x)

/-- The point `(k,j)` of `(ℕ∪{∞}) ⊗ (ℕ∪{∞})`. -/
abbrev mkNS2 (k j : LightProfinite.NatUnionInfty) : ↥NS2 := (k, j)

/-! ## The continuity criterion for maps into `ℕ∪{∞}` -/

/-- The finite points of `ℕ∪{∞}` are clopen. -/
theorem isClopen_singleton_some (n : ℕ) :
    IsClopen ({(OnePoint.some n)} : Set (OnePoint ℕ)) := by
  have h : ({(OnePoint.some n)} : Set (OnePoint ℕ)) = (↑) '' ({n} : Set ℕ) := by
    ext x
    constructor
    · rintro rfl
      exact ⟨n, rfl, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      rw [Set.mem_singleton_iff] at hm
      rw [hm]
      simp
  refine ⟨?_, ?_⟩
  · rw [h, OnePoint.isClosed_image_coe]
    exact ⟨isClosed_discrete _, (Set.finite_singleton n).isCompact⟩
  · rw [h, OnePoint.isOpen_image_coe]
    exact isOpen_discrete _

/-- **Continuity criterion for maps into `ℕ∪{∞}`.**  A function into the one-point
compactification of `ℕ` is continuous if and only if every fibre over a finite point is clopen.
(For a continuous map all singleton fibres are automatically clopen; conversely, the closed subsets
of `ℕ∪{∞}` are the finite subsets of `ℕ` and the subsets containing `∞`, and the preimage of the
former is a finite union of clopens while the preimage of the latter is the complement of a union of
opens.) -/
theorem continuous_onePoint_iff_isClopen {X : Type*} [TopologicalSpace X] (f : X → OnePoint ℕ) :
    Continuous f ↔ ∀ n : ℕ, IsClopen (f ⁻¹' {OnePoint.some n}) := by
  constructor
  · intro hf n
    exact (isClopen_singleton_some n).preimage hf
  · intro h
    rw [continuous_iff_isClosed]
    intro s hs
    by_cases hinf : (∞ : OnePoint ℕ) ∈ s
    · rw [← isOpen_compl_iff]
      have hcompl : (f ⁻¹' s)ᶜ = ⋃ n ∈ {n : ℕ | OnePoint.some n ∉ s},
          f ⁻¹' {OnePoint.some n} := by
        ext x
        simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq,
          Set.mem_singleton_iff]
        constructor
        · intro hx
          by_cases hfx : f x = ∞
          · exact absurd (hfx ▸ hinf) hx
          · obtain ⟨n, hn⟩ := OnePoint.ne_infty_iff_exists.mp hfx
            exact ⟨n, fun hh => hx (hn ▸ hh), hn.symm⟩
        · rintro ⟨n, hn, hfx⟩
          exact fun h => hn (hfx ▸ h)
      rw [hcompl]
      exact isOpen_iUnion fun n => isOpen_iUnion fun _ => (h n).2
    · rw [OnePoint.isClosed_iff_of_notMem hinf] at hs
      have hfin : ((↑) ⁻¹' s : Set ℕ).Finite := hs.2.finite_of_discrete
      have hcompl : f ⁻¹' s = ⋃ n ∈ ((↑) ⁻¹' s : Set ℕ), f ⁻¹' {OnePoint.some n} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_cases hfx : f x = ∞
          · exact absurd (hfx ▸ hx) hinf
          · obtain ⟨n, hn⟩ := OnePoint.ne_infty_iff_exists.mp hfx
            exact ⟨n, hn ▸ hx, hn.symm⟩
        · rintro ⟨n, hn, hfx⟩
          exact hfx ▸ hn
      rw [hcompl]
      exact hfin.isClosed_biUnion fun n _ => (h n).1

/-! ## The maps `ẽ`, `β`, `ψ`, `φ_P` -/

/-- `ẽ(k,x) = e_{k-1} x` for `k ≥ 1`, `ẽ(0,x) = s₀`, `ẽ(∞,x) = x`. -/
def ePredFun (S : LightProfinite.{0}) [Infinite S] (p : ↥(NS S)) : ↥S :=
  p.1.elim p.2 (fun k => if k = 0 then (levelData S).s₀ else e S (k - 1) p.2)

/-- `β(j,x) = e_{n(j)-1} x` (`s₀` when `n(j) = 0`), `β(∞,x) = x`. -/
def betaFun (S : LightProfinite.{0}) [Infinite S] (p : ↥(NS S)) : ↥S :=
  p.1.elim p.2 (fun k => if lvl S k = 0 then (levelData S).s₀ else e S (lvl S k - 1) p.2)

/-- `ψ(k,x) = idx (e_k x)` if `e_k x = a_j` with `n(j) = k` (equivalently: `e_k x` is a point of
level `k` different from `s₀`), and `∞` otherwise; `ψ(∞,x) = ∞`. -/
def psiFun (S : LightProfinite.{0}) [Infinite S] (p : ↥(NS S)) : ℕ∪{∞} := by
  classical
  exact p.1.elim ∞ (fun k =>
    if e S k p.2 ∈ Set.range (levelData S).a ∧ (levelData S).lv (e S k p.2) = k then
      ((levelData S).idx (e S k p.2) : ℕ∪{∞})
    else ∞)

/-- `φ_P(k,j) = j` if `k ≤ n(j)`, and `∞` otherwise (including when `k = ∞` or `j = ∞`). -/
def phiPFun (S : LightProfinite.{0}) [Infinite S] (p : ↥NS2) : ℕ∪{∞} :=
  p.1.elim ∞ fun k => p.2.elim ∞ fun j => if k ≤ lvl S j then (j : ℕ∪{∞}) else ∞

/-! ## Pointwise values -/

variable {S : LightProfinite.{0}} [Infinite S]

@[simp] lemma ePredFun_infty (x : ↥S) : ePredFun S ((∞ : ℕ∪{∞}), x) = x := rfl

@[simp] lemma ePredFun_zero (x : ↥S) :
    ePredFun S (((0 : ℕ) : ℕ∪{∞}), x) = (levelData S).s₀ := by
  simp [ePredFun]

@[simp] lemma ePredFun_succ (k : ℕ) (x : ↥S) :
    ePredFun S (((k + 1 : ℕ) : ℕ∪{∞}), x) = e S k x := by
  simp only [ePredFun, OnePoint.elim_some]
  rw [if_neg (by omega : ¬ (k + 1 = 0))]
  simp

@[simp] lemma betaFun_infty (x : ↥S) : betaFun S ((∞ : ℕ∪{∞}), x) = x := rfl

lemma betaFun_lvl (j : ℕ) (x : ↥S) :
    betaFun S (((j : ℕ) : ℕ∪{∞}), x) =
      (if lvl S j = 0 then (levelData S).s₀ else e S (lvl S j - 1) x) := by
  simp only [betaFun, OnePoint.elim_some]

@[simp] lemma psiFun_infty (x : ↥S) : psiFun S ((∞ : ℕ∪{∞}), x) = ∞ := by
  simp only [psiFun, OnePoint.elim_infty]

lemma psiFun_some_of (k : ℕ) {x : ↥S}
    (h : e S k x ∈ Set.range (levelData S).a ∧ (levelData S).lv (e S k x) = k) :
    psiFun S (((k : ℕ) : ℕ∪{∞}), x) = ((levelData S).idx (e S k x) : ℕ∪{∞}) := by
  simp only [psiFun, OnePoint.elim_some]
  exact if_pos h

lemma psiFun_some_eq_infty (k : ℕ) {x : ↥S}
    (h : ¬ (e S k x ∈ Set.range (levelData S).a ∧ (levelData S).lv (e S k x) = k)) :
    psiFun S (((k : ℕ) : ℕ∪{∞}), x) = ∞ := by
  simp only [psiFun, OnePoint.elim_some]
  exact if_neg h

/-- The defining property of `ψ`: if `e_k x = a_j` and `n(j) = k`, then `ψ(k,x) = j`. -/
lemma psiFun_some_eq (k : ℕ) {x : ↥S} {j : ℕ} (hx : e S k x = (levelData S).a j)
    (hj : lvl S j = k) : psiFun S (((k : ℕ) : ℕ∪{∞}), x) = ((j : ℕ) : ℕ∪{∞}) := by
  rw [psiFun_some_of k ⟨⟨j, hx.symm⟩, by rw [hx]; exact hj⟩]
  rw [hx, (levelData S).idx_a j]

@[simp] lemma phiPFun_infty_left (q : ↥(ℕ∪{∞})) : phiPFun S ((∞ : ℕ∪{∞}), q) = ∞ := rfl

@[simp] lemma phiPFun_some_infty (k : ℕ) :
    phiPFun S (((k : ℕ) : ℕ∪{∞}), (∞ : ℕ∪{∞})) = ∞ := rfl

lemma phiPFun_some_some (k j : ℕ) :
    phiPFun S (((k : ℕ) : ℕ∪{∞}), ((j : ℕ) : ℕ∪{∞})) =
      (if k ≤ lvl S j then ((j : ℕ) : ℕ∪{∞}) else ∞) := by
  simp only [phiPFun, OnePoint.elim_some]

lemma phiPFun_some_some_of_le {k j : ℕ} (h : k ≤ lvl S j) :
    phiPFun S (((k : ℕ) : ℕ∪{∞}), ((j : ℕ) : ℕ∪{∞})) = ((j : ℕ) : ℕ∪{∞}) := by
  rw [phiPFun_some_some, if_pos h]

lemma phiPFun_some_some_of_lt {k j : ℕ} (h : lvl S j < k) :
    phiPFun S (((k : ℕ) : ℕ∪{∞}), ((j : ℕ) : ℕ∪{∞})) = ∞ := by
  rw [phiPFun_some_some, if_neg (by omega)]

lemma phiPFun_eq_infty_iff {k j : ℕ} :
    phiPFun S (((k : ℕ) : ℕ∪{∞}), ((j : ℕ) : ℕ∪{∞})) = ∞ ↔ lvl S j < k := by
  rw [phiPFun_some_some]
  constructor
  · intro h
    by_contra hk
    rw [if_pos (by omega)] at h
    exact OnePoint.coe_ne_infty j h
  · intro h
    rw [if_neg (by omega : ¬ (k ≤ lvl S j))]

/-! ## The subset `T' = {(j,a_j)} ∪ {∞} × S` -/

/-- The closed subset `T' = {(j,a_j) : j ∈ ℕ} ∪ {∞} × S` of `(ℕ∪{∞}) × S`. -/
def tSet (S : LightProfinite.{0}) [Infinite S] : Set ↥(NS S) :=
  {p | p.1 = ∞ ∨ ∃ j : ℕ, p.1 = ((j : ℕ) : ℕ∪{∞}) ∧ p.2 = (levelData S).a j}

variable (S) in
/-- Membership in `T'`. -/
lemma mem_tSet_iff (p : ↥(NS S)) :
    p ∈ tSet S ↔ p.1 = ∞ ∨ ∃ j : ℕ, p.1 = ((j : ℕ) : ℕ∪{∞}) ∧ p.2 = (levelData S).a j :=
  Iff.rfl

lemma mem_tSet_infty (x : ↥S) : ((∞ : ℕ∪{∞}), x) ∈ tSet S := Or.inl rfl

lemma mem_tSet_graph (j : ℕ) :
    ((((j : ℕ) : ℕ∪{∞})), (levelData S).a j) ∈ tSet S := Or.inr ⟨j, rfl, rfl⟩

/-- The second coordinate of a point of `T'` over a finite index is `a_j`. -/
lemma tSet_second_eq {p : ↥(NS S)} (hp : p ∈ tSet S) {j : ℕ} (hj : p.1 = ((j : ℕ) : ℕ∪{∞})) :
    p.2 = (levelData S).a j := by
  rcases hp with h | ⟨j', hj', h2⟩
  · exact absurd (hj ▸ h) (by simp)
  · rw [hj] at hj'
    rw [OnePoint.coe_eq_coe] at hj'
    rw [hj', h2]

end Work.ATOM
