import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG4c.AlBadParDefs
import Submission.Work.WilG4c.AlBadParAux
import Submission.Work.WilG4c.AlBadParThin
import Submission.Work.WilG4c.ThinCellCoverData
import Submission.Work.WilG4c.JBadMem
import Submission.Work.WilG4c.JBadThin
import Submission.Work.WilG4c.SliceLift
import Submission.Work.WilG4c.PullFamGraphMem
import Submission.Work.WilG4a.CD.thinCellParam
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.CD.eval_bind_shift
import Submission.Work.WilG0.API
import Submission.Work.WilG0.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## Elementary `Fin` / fibre bookkeeping -/

/-- The parameter part of a point whose cube part has been overwritten: `parPt` only reads the
first `p` coordinates. -/
theorem parPt_append {p n : ℕ} (l : Fin p → ℝ) (u : Fin (n + 1) → ℝ) :
    Work.WilkG4c.parPt (Fin.append l u) = l := by
  funext i
  simp [Work.WilkG4c.parPt]

/-- `parPt` of a point whose cube coordinates have been overwritten by `Fin.snoc` is unchanged:
`Fin.init` only forgets the value coordinate. -/
theorem parPt_init_snoc {p n : ℕ} (X : Fin (p + (n + 1)) → ℝ) (s : ℝ) :
    Work.WilkG4c.parPt (Fin.init (α := fun _ => ℝ) (Fin.snoc X s)) = Work.WilkG4c.parPt X := by
  funext i
  simp [Work.WilkG4c.parPt, Fin.init, Fin.snoc_castSucc]

/-- `AlBad` depends only on the parameter coordinates: `z ∈ AlBad p n f L` iff the parameter of
`z` lies in the projection `AlBadPar p n f L`.  This is what lets a cell decomposition of
`AlBadPar` be lifted to a cell decomposition of `AlBad`. -/
theorem mem_AlBad_iff_parPt {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ Work.WilkG4c.AlBad p n f L ↔
      Work.WilkG4c.parPt (Fin.init z) ∈ Work.WilkG4c.AlBadPar p n f L := by
  constructor
  · intro hz
    refine ⟨Work.WilkG4c.cubePt (Fin.init z), z (Fin.last (p + (n + 1))), ?_⟩
    have h1 : Fin.append (Work.WilkG4c.parPt (Fin.init z)) (Work.WilkG4c.cubePt (Fin.init z))
        = Fin.init z := Work.WilkG4c.fibPt_cubePt (Fin.init z)
    have h2 : Fin.snoc (Fin.init z) (z (Fin.last (p + (n + 1)))) = z := Fin.snoc_init_self z
    rw [h1, h2]
    exact hz
  · rintro ⟨u, s, hs⟩
    rw [Work.WilkG4c.AlBad] at hs
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
    rw [Work.WilkG4c.mem_AlBadK] at hk
    obtain ⟨y₀, ε, hε, hball⟩ := hk
    rw [Work.WilkG4c.AlBad]
    refine Set.mem_iUnion.mpr ⟨k, by
      rw [Work.WilkG4c.mem_AlBadK]
      refine ⟨y₀, ε, hε, fun y hy => ?_⟩
      have hpar : Work.WilkG4c.parPt (Fin.init (α := fun _ => ℝ)
          (Fin.snoc (Fin.append (Work.WilkG4c.parPt (Fin.init z)) u) s)) =
          Work.WilkG4c.parPt (Fin.init z) := by
        rw [parPt_init_snoc, parPt_append]
      simpa only [Work.WilkG4c.fibPt, hpar] using hball y hy⟩

/-! ## The parameter projection of the bad region is thin -/

/-- `AlBadK p n f k` is the preimage, under the parameter map, of the "bad fibre" set
`BadFib p (n+1) (jBad p n f k)`. -/
theorem mem_AlBadK_iff_badFib {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (k : ℕ)
    (z : Fin (p + (n + 1) + 1) → ℝ) :
    z ∈ Work.WilkG4c.AlBadK p n f k ↔
      Work.WilkG4c.parPt (Fin.init z) ∈ Work.WilG4c.BadFib p (n + 1)
        (Work.WilkG4c.jBad p n f k) :=
  Iff.rfl

/-- The parameter projection of the bad region is the union of the bad-fibre sets of the
joint bad loci `jBad p n f k`, `k ≤ |L|`. -/
theorem AlBadPar_eq_biUnion_badFib (p n : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))) :
    Work.WilkG4c.AlBadPar p n f L
      = ⋃ k : Fin (L.length + 1),
          Work.WilG4c.BadFib p (n + 1) (Work.WilkG4c.jBad p n f k.val) := by
  ext l
  constructor
  · rintro ⟨u, s, hz⟩
    rw [Work.WilkG4c.AlBad] at hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    have h2 : Work.WilkG4c.parPt (Fin.init (α := fun _ => ℝ) (Fin.snoc (Fin.append l u) s)) ∈
        Work.WilG4c.BadFib p (n + 1) (Work.WilkG4c.jBad p n f k.val) := hk
    rwa [Fin.init_snoc, parPt_append] at h2
  · intro hkl
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hkl
    refine ⟨0, 0, ?_⟩
    rw [Work.WilkG4c.AlBad]
    refine Set.mem_iUnion.mpr ⟨k, ?_⟩
    refine (mem_AlBadK_iff_badFib f k.val (Fin.snoc (Fin.append l 0) 0)).mpr ?_
    rwa [Fin.init_snoc, parPt_append]

/-- **The parameter projection of the bad region is thin.**  It is the finite union of the
bad-fibre sets of the joint bad loci, each of which is nowhere dense: `jBad p n f k` is
`Ω`-definable uniformly in `k` (`JBadMem`) with empty interior (`JBadThin`), so the induction
`BadFib_isNowhereDense` applies. -/
theorem AlBadPar_interior_eq_empty (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (p n F0 : ℕ) :
    ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      interior (Work.WilkG4c.AlBadPar p n f L) = ∅ := by
  intro D f L hf
  obtain ⟨a, b, hJb⟩ := Work.WilkG4c.JBadMem S hder p n F0
  have hmem : ∀ k : ℕ,
      Work.WilkG4c.jBad p n f k ∈ S.Ω a (MvPolynomial.eval ![D, k] b) (p + (n + 1)) :=
    fun k => (hJb D k f hf).2
  have hnd : ∀ k : ℕ, IsNowhereDense (Work.WilG4c.BadFib p (n + 1)
      (Work.WilkG4c.jBad p n f k)) := fun k =>
    Work.WilG4c.BadFib_isNowhereDense S hcd (n + 1) p a (MvPolynomial.eval ![D, k] b)
      (Work.WilkG4c.jBad p n f k) (hmem k) (Work.WilG4c.JBadThin S hcd p n F0 D k f hf)
  rw [AlBadPar_eq_biUnion_badFib p n f L]
  refine Set.eq_empty_of_subset_empty (le_trans (interior_mono subset_closure) ?_)
  exact le_of_eq (IsNowhereDense.iUnion (fun k : Fin (L.length + 1) => hnd k.val))

/-! ## Union of a finitely indexed family of `Ω`-sets -/

/-- A `Finset`-indexed union of `Ω F D`-sets is `Ω F (s.card * D)`. -/
theorem union_finset_mem {S : WilkiesDesign.SOMin} {n : ℕ} {σ : Type*} (s : Finset σ)
    (A : σ → Set (Fin n → ℝ)) {F D : ℕ} (h : ∀ i ∈ s, A i ∈ S.Ω F D n) :
    (⋃ i ∈ s, A i) ∈ S.Ω F (s.card * D) n := by
  classical
  set e : ↥s ≃ Fin (Fintype.card ↥s) := Fintype.equivFin ↥s
  set A' : Fin (Fintype.card ↥s) → Set (Fin n → ℝ) := fun i => A ((e.symm i : ↥s) : σ)
  have hmem : ∀ i, A' i ∈ S.Ω F D n := fun i => h _ (e.symm i).2
  have hunion := S.union (fun _ : Fin (Fintype.card ↥s) => D) A' hmem
  have hset : (⋃ i : Fin (Fintype.card ↥s), A' i) = ⋃ i ∈ s, A i := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion₂.mpr ⟨((e.symm i : ↥s) : σ), (e.symm i).2, hi⟩
    · intro hz
      obtain ⟨i, hi, hi2⟩ := Set.mem_iUnion₂.mp hz
      refine Set.mem_iUnion.mpr ⟨e ⟨i, hi⟩, ?_⟩
      have h1 : A' (e ⟨i, hi⟩) = A i := by simp only [A', Equiv.symm_apply_apply]
      rwa [h1]
  rw [hset] at hunion
  have hsum : (∑ _ : Fin (Fintype.card ↥s), D) = s.card * D := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_coe]
  rw [hsum] at hunion
  exact hunion

/-! ## Polynomial bookkeeping -/

/-- Substituting two polynomials into a two-variable polynomial and evaluating. -/
theorem eval_aeval_pair {b g h : MvPolynomial (Fin 2) ℕ} (D r : ℕ) :
    MvPolynomial.eval ![D, r] (MvPolynomial.aeval ![g, h] b) =
      b.eval ![MvPolynomial.eval ![D, r] g, MvPolynomial.eval ![D, r] h] := by
  rw [Work.WilG4a.CD.eval_aeval_eq]
  have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
      ((![g, h] : Fin 2 → MvPolynomial (Fin 2) ℕ) i))
      = ![MvPolynomial.eval ![D, r] g, MvPolynomial.eval ![D, r] h] := by
    funext i
    fin_cases i <;> simp
  rw [hfun]

/-- Substituting a multivariate polynomial into a `ℕ`-polynomial commutes with evaluation. -/
theorem eval_eval₂_C' (b₀ : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r] (Polynomial.eval₂ MvPolynomial.C b₀ c) =
      c.eval (MvPolynomial.eval ![D, r] b₀) := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp

/-! ## One parametrised cell of the thin parameter set -/

/-- The slice derivative graph over a single parametrised cell is `Ω`-definable: on the cylinder
`{z | parPt (Fin.init z) ∈ κ}` the slice at the parameter `parPt (Fin.init z)` agrees with the
slice of the pulled-back family `(u, y) ↦ f (Ψ u) y` at the parameter `parPt (Fin.init z) ∘ e`
(`SliceLift`), so the two coordinate pullbacks coincide.  Both are substitution atoms
(`subst_mem`), costing `+1` for the intersection. -/
private theorem slicePiece_mem (S : WilkiesDesign.SOMin) {p p' n : ℕ} (e : Fin p' ↪ Fin p)
    (κ : Set (Fin p → ℝ)) (Ψ : (Fin p' → ℝ) → (Fin p → ℝ))
    (hsec : ∀ l ∈ κ, Ψ (l ∘ e) = l)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
    {aκ Dκ : ℕ} (hκ : κ ∈ S.Ω aκ Dκ p)
    {aT DT : ℕ}
    (hT : Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L ∈
      S.Ω aT DT (p' + (n + 1) + 1)) :
    (Work.WilkG4c.AlDgListSlice p n f L ∩
        {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) ∈
      S.Ω ((aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
            + (aκ + 2 * ((p + (n + 1) + 1) + p) + 1) + 1)
          ((DT + 2) + (Dκ + 2)) (p + (n + 1) + 1) := by
  -- the pullback of the slice graph of the pulled-back family along `cutIdxHat`
  have h1 : {z : Fin (p + (n + 1) + 1) → ℝ |
      z ∘ Work.WilkG4c.cutIdxHat p p' n e ∈
        Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L} ∈
      S.Ω (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1) (DT + 2)
        (p + (n + 1) + 1) :=
    Work.WilG4a.subst_mem S (Work.WilkG4c.cutIdxHat p p' n e) hT
  -- the cylinder over `κ`
  have h2 : {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ} ∈
      S.Ω (aκ + 2 * ((p + (n + 1) + 1) + p) + 1) (Dκ + 2) (p + (n + 1) + 1) := by
    have h := Work.WilG4a.subst_mem S
      (fun i : Fin p => Fin.castSucc (Fin.castAdd (n + 1) i)) hκ
    have hset : {z : Fin (p + (n + 1) + 1) → ℝ |
        z ∘ (fun i : Fin p => Fin.castSucc (Fin.castAdd (n + 1) i)) ∈ κ} =
        {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ} := by
      ext z
      have hfun : (fun i : Fin p => z (Fin.castSucc (Fin.castAdd (n + 1) i))) =
          Work.WilkG4c.parPt (Fin.init z) := by
        funext i
        simp [Work.WilkG4c.parPt, Fin.init]
      show (fun i : Fin p => z (Fin.castSucc (Fin.castAdd (n + 1) i))) ∈ κ ↔
        Work.WilkG4c.parPt (Fin.init z) ∈ κ
      rw [hfun]
    rwa [hset] at h
  have h1' : ({z : Fin (p + (n + 1) + 1) → ℝ |
      z ∘ Work.WilkG4c.cutIdxHat p p' n e ∈
        Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L} : Set _) ∈
      S.Ω (max (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
        (aκ + 2 * ((p + (n + 1) + 1) + p) + 1)) (DT + 2) (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_FD (le_max_left _ _) le_rfl h1
  have h2' : ({z : Fin (p + (n + 1) + 1) → ℝ |
      Work.WilkG4c.parPt (Fin.init z) ∈ κ} : Set _) ∈
      S.Ω (max (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
        (aκ + 2 * ((p + (n + 1) + 1) + p) + 1)) (Dκ + 2) (p + (n + 1) + 1) :=
    Work.WilG0.Omega_mono_FD (le_max_right _ _) le_rfl h2
  have h3 : ({z : Fin (p + (n + 1) + 1) → ℝ |
        z ∘ Work.WilkG4c.cutIdxHat p p' n e ∈
          Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L} ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) ∈
      S.Ω (max (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
        (aκ + 2 * ((p + (n + 1) + 1) + p) + 1) + 1)
        ((DT + 2) + (Dκ + 2)) (p + (n + 1) + 1) :=
    Work.WilG0.Omega_inter2 h1' h2'
  have hset' : ({z : Fin (p + (n + 1) + 1) → ℝ |
        z ∘ Work.WilkG4c.cutIdxHat p p' n e ∈
          Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L} ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) =
      (Work.WilkG4c.AlDgListSlice p n f L ∩
        {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) := by
    ext z
    constructor
    · rintro ⟨h1z, h2z⟩
      exact ⟨(Work.WilG4c.SliceLift e κ Ψ hsec f L z h2z).mpr h1z, h2z⟩
    · rintro ⟨h1z, h2z⟩
      exact ⟨(Work.WilG4c.SliceLift e κ Ψ hsec f L z h2z).mp h1z, h2z⟩
  rw [← hset']
  refine Work.WilG0.Omega_mono_FD ?_ le_rfl h3
  have hmax := le_max_left (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
    (aκ + 2 * ((p + (n + 1) + 1) + p) + 1)
  have hmax2 := le_max_right (aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
    (aκ + 2 * ((p + (n + 1) + 1) + p) + 1)
  omega

/-! ## The recursion half

The proof combines three inputs:

* `hCover` (from `ThinCellCoverData`): a cylindrical decomposition of `ℝ^p` refining the *thin*
  parameter set, whose cells contained in it are parametrised by `k < p` coordinates;
* `hEmpty` (from `AlBadParInteriorEmpty`): the parameter projection of the bad region is thin;
* `hPiece` (from `SlicePiecePullback`): the slice graph over one parametrised cell is
  `Ω`-definable once the slice graph of the pulled-back family is.

The main statement then follows by the induction hypothesis `ih` applied to each of the
finitely many parametrisations, together with the `Ω`-bookkeeping for the format and the degree
polynomial. -/
private theorem badMem_aux (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (n p : ℕ)
    (hBadPar : ∀ (F0 : ℕ), ∃ (a0 : ℕ) (b0 : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        Work.WilkG4c.AlBadPar p n f L ∈ S.Ω a0 (MvPolynomial.eval ![D, L.length] b0) p)
    (ih : ∀ (p' : ℕ), p' < p → ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p' → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p' + (n + 1) + 1) →
        Work.WilkG4c.AlDgListSlice p' n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p' + (n + 1) + 1))
    (hEmpty : ∀ (F0 D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      interior (Work.WilkG4c.AlBadPar p n f L) = ∅)
    (hCover : ∀ (F0 : ℕ), ∃ (A : ℕ) (aCell : ℕ) (bCard : MvPolynomial (Fin 2) ℕ)
        (bCell bD : Polynomial ℕ),
      ∀ (D : ℕ) (V : Set (Fin p → ℝ)), V ∈ S.Ω F0 D p → interior V = ∅ →
        ∃ C : Finset (Set (Fin p → ℝ)),
          WilkiesDesign.IsCylDecomp p C ∧
          (∀ κ ∈ C, κ ⊆ V ∨ Disjoint κ V) ∧
          C.card ≤ MvPolynomial.eval ![D, 1] bCard ∧
          (∀ κ ∈ C, WilkiesDesign.IsCell p κ) ∧
          (∀ κ ∈ C, κ ∈ S.Ω aCell (bCell.eval D) p) ∧
          (∀ κ ∈ C, κ ⊆ V → ∃ (k : ℕ) (hk : k < p) (e : Fin k ↪ Fin p)
              (Ψ : (Fin k → ℝ) → (Fin p → ℝ)),
            (∀ l ∈ κ, Ψ (l ∘ e) = l) ∧
            Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω A (bD.eval D) (k + p)))
    (hPiece : ∀ {p' : ℕ} (e : Fin p' ↪ Fin p) (κ : Set (Fin p → ℝ))
        (Ψ : (Fin p' → ℝ) → (Fin p → ℝ)) (hsec : ∀ l ∈ κ, Ψ (l ∘ e) = l)
        (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1)))
        {aκ Dκ : ℕ} (hκ : κ ∈ S.Ω aκ Dκ p) {aT DT : ℕ}
        (hT : Work.WilkG4c.AlDgListSlice p' n (fun u y => f (Ψ u) y) L ∈
          S.Ω aT DT (p' + (n + 1) + 1)),
        (Work.WilkG4c.AlDgListSlice p n f L ∩
            {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) ∈
          S.Ω ((aT + 2 * ((p + (n + 1) + 1) + (p' + (n + 1) + 1)) + 1)
                + (aκ + 2 * ((p + (n + 1) + 1) + p) + 1) + 1)
              ((DT + 2) + (Dκ + 2)) (p + (n + 1) + 1)) :
    ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        (Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L)
          ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) := by
  intro F0
  obtain ⟨a0, b0, hAp⟩ := hBadPar F0
  obtain ⟨A0, aCell, bCard, bCell, bD, hCoverF⟩ := hCover a0
  choose aG bG hG using fun k : Fin p => Work.WilG4c.PullFamGraphMem S p (k : ℕ) n (max F0 A0)
  choose aT bT hT using fun k : Fin p => ih (k : ℕ) k.isLt (aG k)
  -- the degree bookkeeping polynomials
  set bDv : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C b0 bD with hbDvdef
  set bCellv : MvPolynomial (Fin 2) ℕ := Polynomial.eval₂ MvPolynomial.C b0 bCell with hbCellvdef
  set e1 : MvPolynomial (Fin 2) ℕ := MvPolynomial.X 0 + bDv with he1def
  set eG : Fin p → MvPolynomial (Fin 2) ℕ :=
    (fun k => MvPolynomial.aeval ![e1, e1] (bG k)) with heGdef
  set eT : Fin p → MvPolynomial (Fin 2) ℕ :=
    (fun k => MvPolynomial.aeval ![eG k, MvPolynomial.X 1] (bT k)) with heTdef
  set βk : Fin p → MvPolynomial (Fin 2) ℕ :=
    (fun k => eT k + bDv + bCellv + MvPolynomial.C 4) with hβkdef
  set Pcard : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.aeval ![b0, MvPolynomial.C 1] bCard with hPcarddef
  -- evaluations of the bookkeeping polynomials
  have hbDv_eval : ∀ D r : ℕ, MvPolynomial.eval ![D, r] bDv =
      bD.eval (MvPolynomial.eval ![D, r] b0) := by
    intro D r
    rw [hbDvdef]
    exact eval_eval₂_C' b0 bD D r
  have hbCellv_eval : ∀ D r : ℕ, MvPolynomial.eval ![D, r] bCellv =
      bCell.eval (MvPolynomial.eval ![D, r] b0) := by
    intro D r
    rw [hbCellvdef]
    exact eval_eval₂_C' b0 bCell D r
  have he1_eval : ∀ D r : ℕ, MvPolynomial.eval ![D, r] e1 =
      D + bD.eval (MvPolynomial.eval ![D, r] b0) := by
    intro D r
    rw [he1def, MvPolynomial.eval_add, MvPolynomial.eval_X, hbDv_eval D r]
    simp
  have heG_eval : ∀ (k : Fin p) (D r : ℕ), MvPolynomial.eval ![D, r] (eG k) =
      (bG k).eval ![D + bD.eval (MvPolynomial.eval ![D, r] b0),
        D + bD.eval (MvPolynomial.eval ![D, r] b0)] := by
    intro k D r
    have h1 : eG k = MvPolynomial.aeval ![e1, e1] (bG k) := by rw [heGdef]
    rw [h1, eval_aeval_pair, he1_eval D r]
  have heT_eval : ∀ (k : Fin p) (D r : ℕ), MvPolynomial.eval ![D, r] (eT k) =
      (bT k).eval ![(bG k).eval ![D + bD.eval (MvPolynomial.eval ![D, r] b0),
        D + bD.eval (MvPolynomial.eval ![D, r] b0)], r] := by
    intro k D r
    have h1 : eT k = MvPolynomial.aeval ![eG k, MvPolynomial.X 1] (bT k) := by rw [heTdef]
    rw [h1, eval_aeval_pair, heG_eval k D r]
    simp
  have hβk_eval : ∀ (k : Fin p) (D r : ℕ), MvPolynomial.eval ![D, r] (βk k) =
      (bT k).eval ![(bG k).eval ![D + bD.eval (MvPolynomial.eval ![D, r] b0),
          D + bD.eval (MvPolynomial.eval ![D, r] b0)], r]
        + bD.eval (MvPolynomial.eval ![D, r] b0)
        + bCell.eval (MvPolynomial.eval ![D, r] b0) + 4 := by
    intro k D r
    rw [hβkdef, MvPolynomial.eval_add, MvPolynomial.eval_add, MvPolynomial.eval_add,
      MvPolynomial.eval_C, heT_eval k D r, hbDv_eval D r, hbCellv_eval D r]
  have hPcard_eval : ∀ D r : ℕ, MvPolynomial.eval ![D, r] Pcard =
      MvPolynomial.eval ![MvPolynomial.eval ![D, r] b0, 1] bCard := by
    intro D r
    rw [hPcarddef, eval_aeval_pair]
    simp
  refine ⟨(∑ k : Fin p, ((aT k + 2 * ((p + (n + 1) + 1) + ((k : ℕ) + (n + 1) + 1)) + 1)
        + (aCell + 2 * ((p + (n + 1) + 1) + p) + 1) + 1)),
      Pcard * (∑ k : Fin p, βk k), ?_⟩
  intro D f L hf
  -- the decomposition refining the parameter projection of `AlBad`
  have hApBad : Work.WilkG4c.AlBadPar p n f L ∈
      S.Ω a0 (MvPolynomial.eval ![D, L.length] b0) p := hAp D f L hf
  have hthin : interior (Work.WilkG4c.AlBadPar p n f L) = ∅ := hEmpty F0 D f L hf
  obtain ⟨C, hCyc, hsep, hcard, hcell, hcellΩ, hparam⟩ :=
    hCoverF (MvPolynomial.eval ![D, L.length] b0) (Work.WilkG4c.AlBadPar p n f L) hApBad hthin
  set T : Finset (Set (Fin p → ℝ)) :=
    C.filter (fun κ => κ ⊆ Work.WilkG4c.AlBadPar p n f L) with hTdef
  -- one cell at a time
  have hpiece : ∀ κ ∈ T, (Work.WilkG4c.AlDgListSlice p n f L ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) ∈
      S.Ω (∑ k : Fin p, ((aT k + 2 * ((p + (n + 1) + 1) + ((k : ℕ) + (n + 1) + 1)) + 1)
            + (aCell + 2 * ((p + (n + 1) + 1) + p) + 1) + 1))
        (∑ k : Fin p, MvPolynomial.eval ![D, L.length] (βk k)) (p + (n + 1) + 1) := by
    intro κ hκT
    obtain ⟨hκC, hκsub⟩ := Finset.mem_filter.mp hκT
    obtain ⟨k, hk, e, Ψ, hsec, hΨ⟩ := hparam κ hκC hκsub
    have hf' : WilkiesDesign.CG.famGraph f ∈ S.Ω (max F0 A0)
        (D + bD.eval (MvPolynomial.eval ![D, L.length] b0)) (p + (n + 1) + 1) :=
      Work.WilG0.Omega_mono_FD (le_max_left _ _) (Nat.le_add_right _ _) hf
    have hΨ' : Work.WilG4a.CD.paramGraph Ψ ∈ S.Ω (max F0 A0)
        (D + bD.eval (MvPolynomial.eval ![D, L.length] b0)) (k + p) :=
      Work.WilG0.Omega_mono_FD (le_max_right _ _) (Nat.le_add_left _ _) hΨ
    have hgraph := hG ⟨k, hk⟩ (D + bD.eval (MvPolynomial.eval ![D, L.length] b0)) f Ψ hf' hΨ'
    have hslice := hT ⟨k, hk⟩
      ((bG ⟨k, hk⟩).eval ![(D + bD.eval (MvPolynomial.eval ![D, L.length] b0)),
        (D + bD.eval (MvPolynomial.eval ![D, L.length] b0))]) (fun u y => f (Ψ u) y) L hgraph
    have hmem := hPiece e κ Ψ hsec f L (hcellΩ κ hκC) hslice
    refine Work.WilG0.Omega_mono_FD ?_ ?_ hmem
    · exact Finset.single_le_sum (f := fun k' : Fin p =>
          ((aT k' + 2 * ((p + (n + 1) + 1) + ((k' : ℕ) + (n + 1) + 1)) + 1)
            + (aCell + 2 * ((p + (n + 1) + 1) + p) + 1) + 1))
        (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨k, hk⟩ : Fin p))
    · refine le_trans ?_ (Finset.single_le_sum (f := fun k' : Fin p =>
          MvPolynomial.eval ![D, L.length] (βk k'))
        (fun i _ => Nat.zero_le _) (Finset.mem_univ (⟨k, hk⟩ : Fin p)))
      rw [hβk_eval ⟨k, hk⟩ D L.length]
      omega
  -- the union of the pieces
  have hUnion := union_finset_mem T
    (fun κ => Work.WilkG4c.AlDgListSlice p n f L ∩
      {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ})
    (fun κ hκ => hpiece κ hκ)
  -- the set identity
  have hset : Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L =
      ⋃ κ ∈ T, (Work.WilkG4c.AlDgListSlice p n f L ∩
        {z : Fin (p + (n + 1) + 1) → ℝ | Work.WilkG4c.parPt (Fin.init z) ∈ κ}) := by
    ext z
    constructor
    · rintro ⟨hslice, hbad⟩
      have hl : Work.WilkG4c.parPt (Fin.init z) ∈ Work.WilkG4c.AlBadPar p n f L :=
        (mem_AlBad_iff_parPt f L z).mp hbad
      obtain ⟨κ, hκC, hκl⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hCyc _
      have hκsub : κ ⊆ Work.WilkG4c.AlBadPar p n f L := by
        rcases hsep κ hκC with h | h
        · exact h
        · exact absurd hl (Set.disjoint_left.mp h hκl)
      exact Set.mem_iUnion₂.mpr ⟨κ, Finset.mem_filter.mpr ⟨hκC, hκsub⟩, hslice, hκl⟩
    · rintro hz
      obtain ⟨κ, hκT, hslice, hκl⟩ := Set.mem_iUnion₂.mp hz
      exact ⟨hslice, (mem_AlBad_iff_parPt f L z).mpr ((Finset.mem_filter.mp hκT).2 hκl)⟩
  rw [hset]
  refine Work.WilG0.Omega_mono_FD le_rfl ?_ hUnion
  rw [MvPolynomial.eval_mul, hPcard_eval D L.length, map_sum]
  refine Nat.mul_le_mul_right _ ?_
  exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) hcard

theorem AlDgListSliceBadMem (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (hder : WilkiesDesign.SOMin.SharpDeriv S) (n p : ℕ)
    (hBadPar : ∀ (F0 : ℕ), ∃ (a0 : ℕ) (b0 : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        Work.WilkG4c.AlBadPar p n f L ∈ S.Ω a0 (MvPolynomial.eval ![D, L.length] b0) p)
    (ih : ∀ (p' : ℕ), p' < p → ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p' → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p' + (n + 1) + 1) →
        Work.WilkG4c.AlDgListSlice p' n f L ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p' + (n + 1) + 1)) :
    ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (L : List (Fin (n + 1))),
        WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
        (Work.WilkG4c.AlDgListSlice p n f L ∩ Work.WilkG4c.AlBad p n f L)
          ∈ S.Ω a (MvPolynomial.eval ![D, L.length] b) (p + (n + 1) + 1) :=
  badMem_aux S hcd hder n p hBadPar ih
    (fun F0 D f L hf => AlBadPar_interior_eq_empty S hcd hder p n F0 D f L hf)
    (fun F0 => Work.WilG4c.ThinCellCoverData S hcd p F0)
    (slicePiece_mem (S := S) (p := p) (n := n))

end Work.WilG4c
