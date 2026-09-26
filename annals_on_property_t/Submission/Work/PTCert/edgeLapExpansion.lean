import Mathlib
import Submission.Work.PTCert.LetterAPI
import Submission.Work.PTCert.EdgeLap.mem_SEdge_b1_iff
import Submission.Work.PTCert.EdgeLap.sum_cEdge_eq

/-!
# The edge Laplacian expanded in the letters

`edgeLap p = Laplacian (SEdge p)` is the Laplacian of the eight Nielsen transvections carried by
the edge `p = {i,j}` (`i < j`): `ρᵢⱼ^{±1}, λᵢⱼ^{±1}, ρⱼᵢ^{±1}, λⱼᵢ^{±1}`.  These eight elements
are exactly the letters `b1 r a`, `1 ≤ a < NB1 r`, whose *unordered* pair `edgeL r a` is the pair
`edgePair p` of the vertices of `p`, so the Laplacian can be rewritten as the `cEdge`-weighted sum
over all letters.

This file collects the auxiliary lemmas (`dirEdge` as the image of the four `Xtr` kinds, its
cardinality and disjointness, the unfolding of a letter `b1 r (1+4q+k)` as a transvection, and the
description of `edgeL` through `pairOf`) and then assembles the expansion.
-/

set_option autoImplicit false

namespace Work.PTCert.EdgeAux

open Submission.PTCert Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

/-- `NB1 r` in the shape used by `omega` (the product `r * (r-1)` is a single atom). -/
lemma NB1_unfold (r : ℕ) : Submission.PTCert.NB1 r = 1 + 4 * (r * (r - 1)) := by
  simp only [Submission.PTCert.NB1, mul_assoc]

/-- The four transvections of an ordered pair are the four `Xtr` kinds. -/
lemma dirEdge_eq_image {r : ℕ} (i j : Fin r) (hij : i ≠ j) :
    dirEdge i j hij = (Finset.range 4).image (fun k => Submission.PTCert.Xtr i j hij k) := by
  ext x
  rw [Edge.mem_dirEdge, Finset.mem_image]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨0, by norm_num, by simp [h]⟩
    · exact ⟨1, by norm_num, by simp [h]⟩
    · exact ⟨2, by norm_num, by simp [h]⟩
    · exact ⟨3, by norm_num, by simp [h]⟩
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.mem_range] at hk
    interval_cases k <;> simp

/-- The transvection set of an edge has eight elements. -/
lemma card_SEdge {r : ℕ} (p : Edge r) : (SEdge p).card = 8 := by
  have hdisj : ∀ (i j : Fin r) (hij : i ≠ j),
      Disjoint (dirEdge i j hij) (dirEdge j i hij.symm) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [dirEdge_eq_image, Finset.mem_image] at hx
    rw [dirEdge_eq_image, Finset.mem_image] at hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hxb⟩ := hy
    have h : Submission.PTCert.Xtr i j hij a = Submission.PTCert.Xtr j i hij.symm b := by
      rw [hxa, ← hxb]
    exact hij (Work.PTCert.XtrInjective i j j i hij hij.symm a b (Finset.mem_range.mp ha)
      (Finset.mem_range.mp hb) h).1
  have hcard : ∀ (i j : Fin r) (hij : i ≠ j), (dirEdge i j hij).card = 4 := by
    intro i j hij
    rw [dirEdge_eq_image, Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb h
      exact (Work.PTCert.XtrInjective i j i j hij hij a b (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb) h).2.2
  rw [SEdge_def, sEdgeOf, Finset.card_union_of_disjoint (hdisj _ _ _), hcard, hcard]

/-- The letter `1 + 4*q + k` (`k < 4`, `q < r*(r-1)`) is the Nielsen transvection of kind `k` on
the ordered pair `pairOf r q`. -/
lemma b1_eq_Xtr_of_pairOf (r q k : ℕ) (hr : 2 ≤ r) (hq : q < r * (r - 1)) (hk : k < 4)
    (i j : Fin r) (hij : i ≠ j) (hpair : pairOf r q = ((i : ℕ), (j : ℕ))) :
    b1 r (1 + 4 * q + k) = Submission.PTCert.Xtr i j hij k := by
  have hsub : 1 + 4 * q + k - 1 = 4 * q + k := by omega
  have hdiv : (4 * q + k) / 4 = q := by
    rw [Nat.mul_add_div (by norm_num : 0 < 4), Nat.div_eq_of_lt hk, Nat.add_zero]
  have hmod : (4 * q + k) % 4 = k := by
    rw [show 4 * q + k = k + 4 * q by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have h1 : 1 ≤ 1 + 4 * q + k := by omega
  have h2 : 1 + 4 * q + k < NB1 r := by rw [NB1_unfold]; omega
  rw [b1_eq_ltr r _ hr h1 h2]
  have hcond : (pairOf r q).1 < r ∧ (pairOf r q).2 < r ∧ (pairOf r q).1 ≠ (pairOf r q).2 := by
    rw [hpair]; exact ⟨i.isLt, j.isLt, fun h => hij (Fin.ext h)⟩
  rw [ltr_eq_Xtr r _ (by rw [hsub, hdiv]; exact hcond) i j hij
    (by rw [hsub, hdiv]; exact hpair.symm)]
  rw [hsub, hmod]

/-- The edge of a letter is the unordered pair `{u,v}` of `pairOf r ((a-1)/4)`. -/
lemma edgeL_eq_edgePair_iff (r : ℕ) (p : Edge r) (a : ℕ) (_ha1 : 1 ≤ a) (_ha2 : a < NB1 r) :
    edgeL r a = edgePair p ↔
      pairOf r ((a - 1) / 4) = ((p.1.1 : ℕ), (p.1.2 : ℕ)) ∨
      pairOf r ((a - 1) / 4) = ((p.1.2 : ℕ), (p.1.1 : ℕ)) := by
  have hlt : (p.1.1 : ℕ) < (p.1.2 : ℕ) := p.2
  simp only [edgeL, edgePair, Prod.mk.injEq]
  constructor
  · rintro ⟨hmn, hmx⟩
    rcases le_total ((pairOf r ((a - 1) / 4)).1) ((pairOf r ((a - 1) / 4)).2) with hle | hle
    · left
      rw [min_eq_left hle] at hmn
      rw [max_eq_right hle] at hmx
      exact Prod.ext hmn hmx
    · right
      rw [min_eq_right hle] at hmn
      rw [max_eq_left hle] at hmx
      exact Prod.ext hmx hmn
  · rintro (h | h)
    · have h1' := congrArg Prod.fst h
      have h2' := congrArg Prod.snd h
      simp only at h1' h2'
      rw [h1', h2']
      exact ⟨min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)⟩
    · have h1' := congrArg Prod.fst h
      have h2' := congrArg Prod.snd h
      simp only at h1' h2'
      rw [h1', h2']
      exact ⟨min_eq_right (le_of_lt hlt), max_eq_left (le_of_lt hlt)⟩

end Work.PTCert.EdgeAux

namespace Work.PTCert

open Submission.PTCert Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

/-- The edge Laplacian expanded in the letters: for an edge `p = {i,j}` (`i < j`),
`edgeLap p = 8•1 - ∑_{g ∈ SEdge p} of g = ∑_{a < NB1 r} cEdge r (i,j) a • of (b1 r a)`.
Proof route: `Edge r` is empty for `r ≤ 1`.  For `r ≥ 2`, `edgeLap p = Laplacian (SEdge p)` and
`SEdge p` is the eight-element set `{ρᵢⱼ^{±1}, λᵢⱼ^{±1}, ρⱼᵢ^{±1}, λⱼᵢ^{±1}}` (`sEdgeOf`, `dirEdge`,
`mem_sEdgeOf`, `mem_dirEdge`).  Its `b1`-preimage is the letter set
`L p = {a ∈ Ico 1 (NB1 r) | edgeL r a = edgePair p}`: a letter `1 + 4*q + kind` lies in `L p` iff
`pairOf r q ∈ {(i,j), (j,i)}`, and there are exactly two such `q` (`pairOfChar`), giving eight letters
`1 + 4*q + kind` (`kind < 4`); `ltr_eq_Xtr`/`b1_eq_ltr` identifies their images with the eight
transvections.  Then `Finset.sum_image` + `b1_injOn` turns `∑_{g ∈ SEdge p} of g` into
`∑_{a ∈ L p} of (b1 r a)`, and `cEdge r e a = 8` at `a = 0`, `= -1` on `L p`, `= 0` elsewhere,
with `b1 r 0 = 1`. -/
theorem edgeLapExpansion (r : ℕ) (p : Submission.RouteB.Edge r) :
    Submission.RouteB.Edge.edgeLap p =
      ∑ a ∈ Finset.range (Submission.PTCert.NB1 r),
        (Submission.PTCert.cEdge r (Submission.PTCert.edgePair p) a : ℝ) •
          MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
  have hr : 2 ≤ r := by
    have h1 := p.1.1.isLt; have h2 := p.1.2.isLt; have h3 := p.2
    omega
  have hneij : (p.1.1 : ℕ) ≠ (p.1.2 : ℕ) := by intro h; have := p.2; omega
  have hneji : (p.1.2 : ℕ) ≠ (p.1.1 : ℕ) := fun h => hneij h.symm
  have hfinij : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hfinji : p.1.2 ≠ p.1.1 := hfinij.symm
  set e : ℕ × ℕ := Submission.PTCert.edgePair p with he
  set L : Finset ℕ := (Finset.Ico 1 (NB1 r)).filter
    (fun a => Submission.PTCert.edgeL r a = e) with hL
  -- the letters of `L` are exactly the `b1`-preimages of `SEdge p`
  have hchar : ∀ a ∈ Finset.Ico 1 (NB1 r),
      (Submission.PTCert.edgeL r a = e ↔ Submission.PTCert.b1 r a ∈ SEdge p) := by
    intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.mp ha
    rw [he, EdgeAux.edgeL_eq_edgePair_iff r p a ha1 ha2,
      Work.PTCert.EdgeLap.mem_SEdge_b1_iff r hr p a ha1 ha2]
  have hL' : L = (Finset.Ico 1 (NB1 r)).filter
      (fun a => Submission.PTCert.b1 r a ∈ SEdge p) := by
    ext a
    simp only [hL, Finset.mem_filter]
    constructor
    · rintro ⟨ha, hla⟩; exact ⟨ha, (hchar a ha).mp hla⟩
    · rintro ⟨ha, hba⟩; exact ⟨ha, (hchar a ha).mpr hba⟩
  -- `b1` maps `L` bijectively onto `SEdge p`
  have himage : L.image (Submission.PTCert.b1 r) = SEdge p := by
    rw [hL']
    apply Finset.Subset.antisymm
    · intro g hg
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hg
      exact (Finset.mem_filter.mp ha).2
    · intro g hg
      have hg0 : g ∈ SEdge p := hg
      rw [SEdge_def, mem_sEdgeOf] at hg
      rcases hg with hg | hg
      · rw [EdgeAux.dirEdge_eq_image] at hg
        obtain ⟨k, hk, hkg⟩ := Finset.mem_image.mp hg
        have hk4 : k < 4 := Finset.mem_range.mp hk
        have hqidx : Work.PTCert.pairIdx r (p.1.1 : ℕ) (p.1.2 : ℕ) < r * (r - 1) :=
          Work.PTCert.pairIdx_lt r _ _ hr p.1.1.isLt p.1.2.isLt hneij
        have hpairof : pairOf r (Work.PTCert.pairIdx r (p.1.1 : ℕ) (p.1.2 : ℕ)) =
            ((p.1.1 : ℕ), (p.1.2 : ℕ)) :=
          Work.PTCert.pairOf_pairIdx p.1.1.isLt p.1.2.isLt hneij
        refine Finset.mem_image.mpr
          ⟨1 + 4 * Work.PTCert.pairIdx r (p.1.1 : ℕ) (p.1.2 : ℕ) + k, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
          · rw [EdgeAux.NB1_unfold]; omega
          · rw [EdgeAux.b1_eq_Xtr_of_pairOf r _ k hr hqidx hk4 p.1.1 p.1.2 hfinij hpairof]
            rw [hkg]
            exact hg0
        · rw [EdgeAux.b1_eq_Xtr_of_pairOf r _ k hr hqidx hk4 p.1.1 p.1.2 hfinij hpairof]
          exact hkg
      · rw [EdgeAux.dirEdge_eq_image] at hg
        obtain ⟨k, hk, hkg⟩ := Finset.mem_image.mp hg
        have hk4 : k < 4 := Finset.mem_range.mp hk
        have hqidx : Work.PTCert.pairIdx r (p.1.2 : ℕ) (p.1.1 : ℕ) < r * (r - 1) :=
          Work.PTCert.pairIdx_lt r _ _ hr p.1.2.isLt p.1.1.isLt hneji
        have hpairof : pairOf r (Work.PTCert.pairIdx r (p.1.2 : ℕ) (p.1.1 : ℕ)) =
            ((p.1.2 : ℕ), (p.1.1 : ℕ)) :=
          Work.PTCert.pairOf_pairIdx p.1.2.isLt p.1.1.isLt hneji
        refine Finset.mem_image.mpr
          ⟨1 + 4 * Work.PTCert.pairIdx r (p.1.2 : ℕ) (p.1.1 : ℕ) + k, ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
          · rw [EdgeAux.NB1_unfold]; omega
          · rw [EdgeAux.b1_eq_Xtr_of_pairOf r _ k hr hqidx hk4 p.1.2 p.1.1 hfinji hpairof]
            rw [hkg]
            exact hg0
        · rw [EdgeAux.b1_eq_Xtr_of_pairOf r _ k hr hqidx hk4 p.1.2 p.1.1 hfinji hpairof]
          exact hkg
  have hsum : ∑ g ∈ SEdge p, MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) g
      = ∑ a ∈ L, MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r a) := by
    rw [← himage]
    rw [Finset.sum_image]
    intro x hx y hy hxy
    rw [hL'] at hx hy
    exact b1_injOn r hr (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  have hcardNat : Nat.card (SEdge p) = 8 := by
    have h : Nat.card (SEdge p) = (SEdge p).card := by simp
    rw [h, EdgeAux.card_SEdge]
  have h8 : (Nat.card (SEdge p) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
      = (8 : ℝ) • (1 : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r)))) := by
    rw [hcardNat]
    rw [Algebra.smul_def, mul_one]
    rw [show (algebraMap ℝ (MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))) (8 : ℝ)
        = MonoidAlgebra.single (1 : MulAut (FreeGroup (Fin r))) (8 : ℝ) by simp]
    exact (MonoidAlgebra.ofNat_def 8).symm
  rw [show Submission.RouteB.Edge.edgeLap p
      = (Nat.card (SEdge p) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))))
        - ∑ g ∈ SEdge p, MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) g from rfl]
  rw [h8, Work.PTCert.EdgeLap.sum_cEdge_eq r (Submission.PTCert.edgePair p)]
  rw [← he, ← hL]
  rw [hsum]

end Work.PTCert
