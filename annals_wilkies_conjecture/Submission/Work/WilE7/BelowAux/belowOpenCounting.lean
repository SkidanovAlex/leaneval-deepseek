/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowOpenCounting`): the **counting** semi-Pfaffian
  presentation of the open lower band `{x ∈ C, -1 < t < (s 0 x) last}`.

  The `Star` half of the open lower band comes from the connected component of `belowSopen`
  (bounded format), but `SubPf` must not use a connected component: instead one *counts the fibre
  points*.  Over `x ∈ C` the fibre of `S.X.set` has exactly `k` points (`hcard`), and `k` of them
  are exhibited explicitly (`hsub`), so

    `t < (s 0 x) last`  ⟺  `-1 < t` and there are `k` fibre points above `t`;

  and the right hand side is a *positive* (existential) condition, hence semi-Pfaffian.

  Concretely, with `C = projFirst p mc '' Cc.set` (`hCpf`), the presentation is

  `ocW = {z : ℝ^{(p+1) + ((p+mc) + (p+(m+1))*k)} |
      (base, t) = projFirst (p+1) _ z ∈ cubeC (p+1) ∧  Cc-part ∈ Cc.set ∧
      ∀ i, block i ∈ S.X.set ∧  base of every block = base of z ∧
      -1 < t ∧ t < last(block 0) ∧ ∀ i < j, last(block i) < last(block j)}`

  built as `SemiPf.prod (cubeSemiPf (p+1)) (SemiPf.prod Cc (iterProd S.X k))` cut by the
  diagonal equations and the strict atoms (`SemiPf.addConds`).  Its projection to the first
  `p+1` coordinates is exactly the open lower band.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.BelowAux.kProd
import Submission.Work.WilE7.BelowAux.kProd_spec
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.pad_proj
import Submission.Work.WilE7.projFirst_fiberClosure
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7

/-! ## §1. Dimensions and coordinate indices -/

/-- The ambient dimension of one copy of `S.X`. -/
abbrev ocNb (p m : ℕ) : ℕ := p + (m + 1)

/-- The dimension of the "rest" block (`Cc` together with the `k` copies of `S.X`). -/
abbrev ocR (p m mc k : ℕ) : ℕ := (p + mc) + ocNb p m * k

/-- The ambient dimension of the counting presentation. -/
abbrev ocN (p m mc k : ℕ) : ℕ := (p + 1) + ocR p m mc k

/-- The index of the `l`-th base coordinate (a `Fin.castAdd`-shape, so that `Fin.append_left`
applies). -/
def ocGbIdx (p m mc k : ℕ) (l : Fin p) : Fin (ocN p m mc k) :=
  Fin.castAdd (ocR p m mc k) (Fin.castSucc l)

/-- The index of the vertical coordinate `t`. -/
def ocGtIdx (p m mc k : ℕ) : Fin (ocN p m mc k) :=
  Fin.castAdd (ocR p m mc k) (Fin.last p)

/-- The index of the `j`-th coordinate of the `Cc`-block. -/
def ocGcIdx (p m mc k : ℕ) (j : Fin (p + mc)) : Fin (ocN p m mc k) :=
  Fin.natAdd (p + 1) (Fin.castAdd (ocNb p m * k) j)

/-- The index of the `l`-th coordinate of the `i`-th copy of `S.X`. -/
def ocGzIdx (p m mc k : ℕ) (i : Fin k) (l : Fin (ocNb p m)) : Fin (ocN p m mc k) :=
  Fin.natAdd (p + 1) (Fin.natAdd (p + mc) (blkIdx i l))

/-- The last coordinate of a block of `S.X`. -/
abbrev ocLastIdx (p m : ℕ) : Fin (ocNb p m) := Fin.natAdd p (Fin.last m)

/-! ## §2. The coordinate extractions -/

/-- The "base + vertical" part of a point of the counting presentation. -/
def ocB {p m mc k : ℕ} (z : Fin (ocN p m mc k) → ℝ) : Fin (p + 1) → ℝ :=
  projFirst (p + 1) (ocR p m mc k) z

/-- The "rest" part (`Cc`-block followed by the copies of `S.X`). -/
def ocZ {p m mc k : ℕ} (z : Fin (ocN p m mc k) → ℝ) : Fin (ocR p m mc k) → ℝ :=
  projSnd (p + 1) (ocR p m mc k) z

/-- The `Cc`-block. -/
def ocC {p m mc k : ℕ} (z : Fin (ocN p m mc k) → ℝ) : Fin (p + mc) → ℝ :=
  projFirst (p + mc) (ocNb p m * k) (ocZ z)

/-- The `k` copies of `S.X`. -/
def ocZf {p m mc k : ℕ} (z : Fin (ocN p m mc k) → ℝ) : Fin (ocNb p m * k) → ℝ :=
  projSnd (p + mc) (ocNb p m * k) (ocZ z)

/-- The `i`-th copy of `S.X` inside a point of the counting presentation. -/
def ocZblk {p m mc k : ℕ} (z : Fin (ocN p m mc k) → ℝ) (i : Fin k) : Fin (ocNb p m) → ℝ :=
  blk i (ocZf z)

/-! ## §3. The coordinate indices read off the extractions -/

theorem ocB_gbIdx (p m mc k : ℕ) (z : Fin (ocN p m mc k) → ℝ) (l : Fin p) :
    z (ocGbIdx p m mc k l) = Fin.init (ocB z) l := rfl

theorem ocB_gtIdx (p m mc k : ℕ) (z : Fin (ocN p m mc k) → ℝ) :
    z (ocGtIdx p m mc k) = ocB z (Fin.last p) := rfl

theorem ocZ_gcIdx (p m mc k : ℕ) (z : Fin (ocN p m mc k) → ℝ) (j : Fin (p + mc)) :
    z (ocGcIdx p m mc k j) = ocC z j := rfl

theorem ocZ_gzIdx (p m mc k : ℕ) (z : Fin (ocN p m mc k) → ℝ) (i : Fin k)
    (l : Fin (ocNb p m)) :
    z (ocGzIdx p m mc k i l) = ocZblk z i l := rfl

/-! ## §4. The cutting polynomials -/

/-- The equation `base = (Cc-block)`. -/
def ocBaseEq (p m mc k r : ℕ) (l : Fin p) : EAPoly (ocN p m mc k) r :=
  MvPolynomial.X (Sum.inl (ocGbIdx p m mc k l)) -
    MvPolynomial.X (Sum.inl (ocGcIdx p m mc k (Fin.castAdd mc l)))

/-- The equation `base = (base of the i-th copy of S.X)`. -/
def ocBlockEq (p m mc k r : ℕ) (i : Fin k) (l : Fin p) : EAPoly (ocN p m mc k) r :=
  MvPolynomial.X (Sum.inl (ocGbIdx p m mc k l)) -
    MvPolynomial.X (Sum.inl (ocGzIdx p m mc k i (Fin.castAdd (m + 1) l)))

/-- The strict atom `t + 1 > 0`. -/
def ocTAtom (p m mc k r : ℕ) : EAPoly (ocN p m mc k) r :=
  MvPolynomial.X (Sum.inl (ocGtIdx p m mc k)) + MvPolynomial.C (1 : ℝ)

/-- The strict atom `t < last(block 0)`. -/
def ocLowAtom (p m mc k r : ℕ) (hk : 0 < k) : EAPoly (ocN p m mc k) r :=
  MvPolynomial.X (Sum.inl (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m))) -
    MvPolynomial.X (Sum.inl (ocGtIdx p m mc k))

/-- The strict atom `last(block i) < last(block j)` for the pair `i < j`: it is the
polynomial `last(j) - last(i)`, positive exactly when the last coordinates increase. -/
def ocLtAtom (p m mc k r : ℕ) (c : Fin k × Fin k) : EAPoly (ocN p m mc k) r :=
  MvPolynomial.X (Sum.inl (ocGzIdx p m mc k c.2 (ocLastIdx p m))) -
    MvPolynomial.X (Sum.inl (ocGzIdx p m mc k c.1 (ocLastIdx p m)))

/-- The list of diagonal equations. -/
def ocE (p m mc k r : ℕ) : List (EAPoly (ocN p m mc k) r) :=
  (((List.finRange k).product (List.finRange p)).map
      (fun c => ocBlockEq p m mc k r c.1 c.2)) ++
    ((List.finRange p).map (fun l => ocBaseEq p m mc k r l))

/-- The pairs `i < j` of sheet indices. -/
def ocPairs (k : ℕ) : List (Fin k × Fin k) :=
  ((List.finRange k).product (List.finRange k)).filter
    (fun c => decide (c.1.val < c.2.val))

/-- The list of strict atoms. -/
def ocP (p m mc k r : ℕ) (hk : 0 < k) : List (EAPoly (ocN p m mc k) r) :=
  [ocTAtom p m mc k r, ocLowAtom p m mc k r hk] ++
    ((ocPairs k).map (fun c => ocLtAtom p m mc k r c))

/-! ## §5. The counting presentation -/

/-- The product `cube × Cc × (S.X)^k`. -/
noncomputable def ocW0 (p m mc k : ℕ) (Cc : SemiPf (p + mc)) (Z : SemiPf (p + (m + 1))) :
    SemiPf (ocN p m mc k) :=
  SemiPf.prod (Work.WilE8.cubeSemiPf (p + 1)) (SemiPf.prod Cc (iterProd Z k))

/-- The counting presentation of the open lower band. -/
noncomputable def ocW (p m mc k : ℕ) (Cc : SemiPf (p + mc)) (Z : SemiPf (p + (m + 1)))
    (hk : 0 < k) : SemiPf (ocN p m mc k) :=
  SemiPf.addConds (ocW0 p m mc k Cc Z)
    (ocE p m mc k (ocW0 p m mc k Cc Z).r) (ocP p m mc k (ocW0 p m mc k Cc Z).r hk)

/-! ## §6. The values of the cutting polynomials -/

theorem eaEval_ocBaseEq {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r) (l : Fin p)
    (z : Fin (ocN p m mc k) → ℝ) :
    eaEval c (ocBaseEq p m mc k r l) z =
      z (ocGbIdx p m mc k l) - z (ocGcIdx p m mc k (Fin.castAdd mc l)) := by
  simp [ocBaseEq, eaEval]

theorem eaEval_ocBlockEq {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r) (i : Fin k)
    (l : Fin p) (z : Fin (ocN p m mc k) → ℝ) :
    eaEval c (ocBlockEq p m mc k r i l) z =
      z (ocGbIdx p m mc k l) - z (ocGzIdx p m mc k i (Fin.castAdd (m + 1) l)) := by
  simp [ocBlockEq, eaEval]

theorem eaEval_ocTAtom {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r)
    (z : Fin (ocN p m mc k) → ℝ) :
    eaEval c (ocTAtom p m mc k r) z = z (ocGtIdx p m mc k) + 1 := by
  simp [ocTAtom, eaEval]

theorem eaEval_ocLowAtom {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r) (hk : 0 < k)
    (z : Fin (ocN p m mc k) → ℝ) :
    eaEval c (ocLowAtom p m mc k r hk) z =
      z (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m)) - z (ocGtIdx p m mc k) := by
  simp [ocLowAtom, eaEval]

theorem eaEval_ocLtAtom {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r)
    (c' : Fin k × Fin k) (z : Fin (ocN p m mc k) → ℝ) :
    eaEval c (ocLtAtom p m mc k r c') z =
      z (ocGzIdx p m mc k c'.2 (ocLastIdx p m)) -
        z (ocGzIdx p m mc k c'.1 (ocLastIdx p m)) := by
  simp [ocLtAtom, eaEval]

/-! ## §7. The diagonal equations -/

theorem ocE_forall {p m mc k r : ℕ} (c : EAChain (ocN p m mc k) r)
    (z : Fin (ocN p m mc k) → ℝ) :
    (∀ f ∈ ocE p m mc k r, eaEval c f z = 0) ↔
      ((∀ i : Fin k, ∀ l : Fin p,
          z (ocGbIdx p m mc k l) = z (ocGzIdx p m mc k i (Fin.castAdd (m + 1) l))) ∧
       (∀ l : Fin p, z (ocGbIdx p m mc k l) = z (ocGcIdx p m mc k (Fin.castAdd mc l)))) := by
  rw [ocE, List.forall_mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro i l
      have hm : ocBlockEq p m mc k r i l ∈
          ((List.finRange k).product (List.finRange p)).map
            (fun c => ocBlockEq p m mc k r c.1 c.2) :=
        List.mem_map.mpr ⟨(i, l),
          List.mem_product.mpr ⟨List.mem_finRange i, List.mem_finRange l⟩, rfl⟩
      have hh := h1 _ hm
      rw [eaEval_ocBlockEq] at hh
      linarith
    · intro l
      have hm : ocBaseEq p m mc k r l ∈
          (List.finRange p).map (fun l => ocBaseEq p m mc k r l) :=
        List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩
      have hh := h2 _ hm
      rw [eaEval_ocBaseEq] at hh
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · intro f hf
      obtain ⟨c', -, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_ocBlockEq, h1 c'.1 c'.2]; ring
    · intro f hf
      obtain ⟨l, -, rfl⟩ := List.mem_map.mp hf
      rw [eaEval_ocBaseEq, h2 l]; ring

/-! ## §8. The strict atoms -/

theorem mem_ocPairs {k : ℕ} (c : Fin k × Fin k) :
    c ∈ ocPairs k ↔ c.1.val < c.2.val := by
  rw [ocPairs, List.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    simpa using h
  · intro h
    exact ⟨List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩,
      by simpa using h⟩

theorem ocP_forall {p m mc k r : ℕ} (hk : 0 < k) (c : EAChain (ocN p m mc k) r)
    (z : Fin (ocN p m mc k) → ℝ) :
    (∀ g ∈ ocP p m mc k r hk, 0 < eaEval c g z) ↔
      (0 < z (ocGtIdx p m mc k) + 1 ∧
       0 < z (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m)) - z (ocGtIdx p m mc k) ∧
       (∀ i j : Fin k, i.val < j.val →
          0 < z (ocGzIdx p m mc k j (ocLastIdx p m)) -
            z (ocGzIdx p m mc k i (ocLastIdx p m)))) := by
  rw [ocP, List.forall_mem_append]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · have hh := h1 (ocTAtom p m mc k r) (by simp)
      rwa [eaEval_ocTAtom] at hh
    · have hh := h1 (ocLowAtom p m mc k r hk) (by simp)
      rwa [eaEval_ocLowAtom] at hh
    · intro i j hij
      have hmem : (i, j) ∈ ocPairs k := (mem_ocPairs (i, j)).mpr hij
      have hh := h2 _ (List.mem_map.mpr ⟨(i, j), hmem, rfl⟩)
      rwa [eaEval_ocLtAtom] at hh
  · rintro ⟨h1, h2, h3⟩
    constructor
    · intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · rw [eaEval_ocTAtom]; exact h1
      · rw [eaEval_ocLowAtom]; exact h2
    · intro g hg
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hg
      rw [eaEval_ocLtAtom]
      exact h3 c'.1 c'.2 ((mem_ocPairs c').mp hc')

/-! ## §9. Membership in the counting presentation -/

theorem ocW_mem_iff {p m mc k : ℕ} (Cc : SemiPf (p + mc)) (Z : SemiPf (p + (m + 1)))
    (hk : 0 < k) (z : Fin (ocN p m mc k) → ℝ) :
    z ∈ (ocW p m mc k Cc Z hk).set ↔
      (ocB z ∈ cubeC (p + 1) ∧ ocC z ∈ Cc.set ∧
       (∀ i : Fin k, ocZblk z i ∈ Z.set) ∧
       (∀ i : Fin k, ∀ l : Fin p,
          z (ocGbIdx p m mc k l) = z (ocGzIdx p m mc k i (Fin.castAdd (m + 1) l))) ∧
       (∀ l : Fin p, z (ocGbIdx p m mc k l) = z (ocGcIdx p m mc k (Fin.castAdd mc l))) ∧
       (0 < z (ocGtIdx p m mc k) + 1) ∧
       (0 < z (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m)) - z (ocGtIdx p m mc k)) ∧
       (∀ i j : Fin k, i.val < j.val →
          0 < z (ocGzIdx p m mc k j (ocLastIdx p m)) -
            z (ocGzIdx p m mc k i (ocLastIdx p m)))) := by
  have h0 : z ∈ (ocW0 p m mc k Cc Z).set ↔
      (ocB z ∈ cubeC (p + 1) ∧ ocC z ∈ Cc.set ∧ (∀ i : Fin k, ocZblk z i ∈ Z.set)) := by
    have hiter : projSnd (p + mc) (ocNb p m * k) (projSnd (p + 1) (ocR p m mc k) z) ∈
        (iterProd Z k).set ↔ ∀ i : Fin k, ocZblk z i ∈ Z.set := by
      rw [iterProd_set]; rfl
    have houter : z ∈ (ocW0 p m mc k Cc Z).set ↔
        (projFirst (p + 1) (ocR p m mc k) z ∈ (Work.WilE8.cubeSemiPf (p + 1)).set ∧
         projSnd (p + 1) (ocR p m mc k) z ∈ (SemiPf.prod Cc (iterProd Z k)).set) := by
      simp only [ocW0, prodSet (Work.WilE8.cubeSemiPf (p + 1)) (SemiPf.prod Cc (iterProd Z k)),
        Set.mem_ofPred_eq]
    have hinner : projSnd (p + 1) (ocR p m mc k) z ∈ (SemiPf.prod Cc (iterProd Z k)).set ↔
        (projFirst (p + mc) (ocNb p m * k) (projSnd (p + 1) (ocR p m mc k) z) ∈ Cc.set ∧
         projSnd (p + mc) (ocNb p m * k) (projSnd (p + 1) (ocR p m mc k) z) ∈
           (iterProd Z k).set) := by
      simp only [prodSet Cc (iterProd Z k), Set.mem_ofPred_eq]
    rw [houter, hinner, hiter, Work.WilE8.cubeSemiPf_set]
    exact ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  have hmem : z ∈ (ocW p m mc k Cc Z hk).set ↔
      (z ∈ (ocW0 p m mc k Cc Z).set ∧
       (∀ f ∈ ocE p m mc k (ocW0 p m mc k Cc Z).r,
          eaEval (ocW0 p m mc k Cc Z).c f z = 0) ∧
       (∀ g ∈ ocP p m mc k (ocW0 p m mc k Cc Z).r hk,
          0 < eaEval (ocW0 p m mc k Cc Z).c g z)) := by
    rw [ocW, SemiPf.addConds_set]
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [hmem, h0, ocE_forall (ocW0 p m mc k Cc Z).c z,
    ocP_forall hk (ocW0 p m mc k Cc Z).c z]
  tauto

/-! ## §10. Consequences of `SemiPf.set` -/

theorem mem_cubeC_of_mem_set {n : ℕ} {X : SemiPf n} {x : Fin n → ℝ} (hx : x ∈ X.set) :
    x ∈ cubeC n := hx.1

theorem append_last {p m : ℕ} (x : Fin p → ℝ) (v : Fin (m + 1) → ℝ) :
    Fin.append x v (ocLastIdx p m) = v (Fin.last m) :=
  Fin.append_right x v (Fin.last m)

/-! ## §11. The projection of the counting presentation is the open lower band -/

theorem ocW_proj_subset {p m mc k : ℕ} (Cc : SemiPf (p + mc)) (Z : SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCc : C = projFirst p mc '' Cc.set) (hk : 0 < k)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ Z.set)
    (hcard : ∀ x ∈ C, (fiber Z.set x).ncard = k) :
    projFirst (p + 1) (ocR p m mc k) '' (ocW p m mc k Cc Z hk).set ⊆
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨-, hCc0, hblk, hBlkEq, hBaseEq, ht, hlow, hlt⟩ :=
    (ocW_mem_iff (p := p) (m := m) (mc := mc) (k := k) Cc Z hk z).mp hz
  -- the base point
  set x : Fin p → ℝ := Fin.init (ocB z) with hxdef
  have hxC : x ∈ C := by
    have hproj : projFirst p mc (ocC z) = x := by
      funext l
      exact (hBaseEq l).symm
    rw [hCc]
    exact ⟨ocC z, hCc0, hproj⟩
  -- the `k` fibre points
  set w : Fin k → Fin (m + 1) → ℝ := fun i => projSnd p (m + 1) (ocZblk z i) with hwdef
  have hwfib : ∀ i, w i ∈ fiber Z.set x := by
    intro i
    rw [mem_fiber_iff]
    have hbase : projFirst p (m + 1) (ocZblk z i) = x := by
      funext l
      exact (hBlkEq i l).symm
    rw [← hbase, append_projFirst_projSnd]
    exact hblk i
  have hwinj : Function.Injective w := by
    intro i j heq
    by_contra hne
    have hv : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hv with h | h
    · have hh : z (ocGzIdx p m mc k i (ocLastIdx p m)) <
          z (ocGzIdx p m mc k j (ocLastIdx p m)) := sub_pos.mp (hlt i j h)
      exact absurd (congrArg (fun f : Fin (m + 1) → ℝ => f (Fin.last m)) heq) (ne_of_lt hh)
    · have hh : z (ocGzIdx p m mc k j (ocLastIdx p m)) <
          z (ocGzIdx p m mc k i (ocLastIdx p m)) := sub_pos.mp (hlt j i h)
      exact absurd (congrArg (fun f : Fin (m + 1) → ℝ => f (Fin.last m)) heq.symm)
        (ne_of_lt hh)
  have hrange : Set.range w = fiber Z.set x := by
    refine Set.eq_of_subset_of_ncard_le (fun y hy => ?_) ?_ ?_
    · obtain ⟨i, rfl⟩ := hy
      exact hwfib i
    · have h1 : (Set.range w).ncard = k := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hwinj, Set.ncard_univ, Nat.card_fin]
      rw [hcard x hxC, h1]
    · exact Set.finite_of_ncard_ne_zero (by rw [hcard x hxC]; omega)
  -- the canonical fibre point `s 0 x`
  have hw0 : projSnd p (m + 1) (Fin.append x (s ⟨0, hk⟩ x)) ∈ Set.range w := by
    rw [hrange, mem_fiber_iff, projSnd_append]
    exact hsub ⟨0, hk⟩ x hxC
  obtain ⟨i, hi⟩ := hw0
  have hwi : (s ⟨0, hk⟩ x) (Fin.last m) = z (ocGzIdx p m mc k i (ocLastIdx p m)) := by
    have h1 : w i = s ⟨0, hk⟩ x := by rw [hi, projSnd_append]
    rw [← h1]
    rfl
  have h0i : z (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m)) ≤
      z (ocGzIdx p m mc k i (ocLastIdx p m)) := by
    rcases eq_or_lt_of_le (Nat.zero_le i.val) with h | h
    · have : i = ⟨0, hk⟩ := Fin.ext h.symm
      rw [this]
    · exact le_of_lt (sub_pos.mp (hlt ⟨0, hk⟩ i h))
  refine ⟨?_, ?_, ?_⟩
  · show Fin.init (ocB z) ∈ C
    exact hxC
  · show -1 < z (ocGtIdx p m mc k)
    linarith
  · calc projFirst (p + 1) (ocR p m mc k) z (Fin.last p) = z (ocGtIdx p m mc k) := rfl
      _ < z (ocGzIdx p m mc k ⟨0, hk⟩ (ocLastIdx p m)) := sub_pos.mp hlow
      _ ≤ z (ocGzIdx p m mc k i (ocLastIdx p m)) := h0i
      _ = (s ⟨0, hk⟩ x) (Fin.last m) := hwi.symm

theorem ocW_proj_superset {p m mc k : ℕ} (Cc : SemiPf (p + mc)) (Z : SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCc : C = projFirst p mc '' Cc.set) (hk : 0 < k)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ Z.set)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} ⊆
      projFirst (p + 1) (ocR p m mc k) '' (ocW p m mc k Cc Z hk).set := by
  intro y hy
  obtain ⟨hyC, hy1, hy2⟩ := hy
  set x : Fin p → ℝ := Fin.init y with hxdef
  have hxC : x ∈ C := hyC
  -- a point of `Cc` over `x`
  obtain ⟨c, hc, hcx⟩ : ∃ c ∈ Cc.set, projFirst p mc c = x := by
    have h := hyC; rw [hCc] at h; exact h
  -- the `k` blocks
  have hCsub : C ⊆ cubeC p := by
    intro w hw
    rw [hCc] at hw
    obtain ⟨d, hd, rfl⟩ := hw
    intro l
    exact (mem_cubeC_of_mem_set hd) (Fin.castAdd mc l)
  have hcxl : ∀ l : Fin p, Fin.init y l = c (Fin.castAdd mc l) := by
    intro l
    rw [← hxdef, ← hcx]
    rfl
  set U : Fin k → Fin (ocNb p m) → ℝ := fun i => Fin.append x (s i x) with hUdef
  have hU : ∀ i, U i ∈ Z.set := by
    intro i; rw [hUdef]; exact hsub i x hxC
  obtain ⟨zf, -, hzfb⟩ := iterProd_surj Z k U hU
  set z0 : Fin (ocN p m mc k) → ℝ := Fin.append y (Fin.append c zf) with hz0def
  -- the values of the coordinates of `z0`
  have hzB : ocB z0 = y := by
    show projFirst (p + 1) (ocR p m mc k) z0 = y
    rw [hz0def]; exact projFirst_append y (Fin.append c zf)
  have hzC : ocC z0 = c := by
    show projFirst (p + mc) (ocNb p m * k) (projSnd (p + 1) (ocR p m mc k) z0) = c
    rw [hz0def, projSnd_append, projFirst_append]
  have hzZf : ocZf z0 = zf := by
    show projSnd (p + mc) (ocNb p m * k) (projSnd (p + 1) (ocR p m mc k) z0) = zf
    rw [hz0def, projSnd_append, projSnd_append]
  have hzblk : ∀ i : Fin k, ocZblk z0 i = U i := by
    intro i
    show blk i (ocZf z0) = U i
    rw [hzZf, hzfb i]
  have hz_gb : ∀ l : Fin p, z0 (ocGbIdx p m mc k l) = Fin.init y l := by
    intro l
    rw [hz0def]
    show Fin.append y (Fin.append c zf) (Fin.castAdd (ocR p m mc k) (Fin.castSucc l))
      = Fin.init y l
    exact Fin.append_left y (Fin.append c zf) (Fin.castSucc l)
  have hz_gt : z0 (ocGtIdx p m mc k) = y (Fin.last p) := by
    rw [hz0def]
    show Fin.append y (Fin.append c zf) (Fin.castAdd (ocR p m mc k) (Fin.last p))
      = y (Fin.last p)
    exact Fin.append_left y (Fin.append c zf) (Fin.last p)
  have hz_gc : ∀ j : Fin (p + mc), z0 (ocGcIdx p m mc k j) = c j := by
    intro j
    rw [hz0def]
    show Fin.append y (Fin.append c zf)
      (Fin.natAdd (p + 1) (Fin.castAdd (ocNb p m * k) j)) = c j
    rw [Fin.append_right, Fin.append_left]
  have hz_gz : ∀ (i : Fin k) (l : Fin (ocNb p m)),
      z0 (ocGzIdx p m mc k i l) = U i l := by
    intro i l
    rw [hz0def]
    show Fin.append y (Fin.append c zf)
      (Fin.natAdd (p + 1) (Fin.natAdd (p + mc) (blkIdx i l))) = U i l
    rw [Fin.append_right, Fin.append_right, ← hzfb i]
    rfl
  have hz_last : ∀ i : Fin k,
      z0 (ocGzIdx p m mc k i (ocLastIdx p m)) = (s i x) (Fin.last m) := by
    intro i
    rw [hz_gz i (ocLastIdx p m), hUdef]
    exact append_last x (s i x)
  refine ⟨z0, ?_, ?_⟩
  · rw [ocW_mem_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzB]
      intro l
      rcases Fin.eq_castSucc_or_eq_last l with ⟨i, rfl⟩ | rfl
      · have hyy : y (Fin.castSucc i) = x i := by rw [hxdef]; rfl
        rw [hyy]
        exact hCsub hxC i
      · have hle : (s ⟨0, hk⟩ x) (Fin.last m) ≤ 1 := by
          have hh := mem_cubeC_of_mem_set (hU ⟨0, hk⟩) (ocLastIdx p m)
          rw [hUdef] at hh
          dsimp only at hh
          rw [append_last] at hh
          exact le_trans (le_abs_self _) hh
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
    · rw [hzC]; exact hc
    · intro i; rw [hzblk i]; exact hU i
    · intro i l
      rw [hz_gb l, hz_gz i (Fin.castAdd (m + 1) l), hUdef, hxdef]
      exact (Fin.append_left (Fin.init y) (s i (Fin.init y)) l).symm
    · intro l
      rw [hz_gb l, hz_gc (Fin.castAdd mc l)]
      exact hcxl l
    · rw [hz_gt]; linarith
    · rw [sub_pos, hz_gt, hz_last ⟨0, hk⟩]; exact hy2
    · intro i j hij
      rw [sub_pos, hz_last i, hz_last j]
      exact hlvl x hxC hij
  · rw [hz0def]; exact projFirst_append y (Fin.append c zf)

/-! ## §12. The open lower band is sub-Pfaffian -/

theorem belowOpenCell_subPf {p m : ℕ} (S : Stratum p (m + 1)) (C : Set (Fin p → ℝ))
    (hCpf : SubPf p C) (k : ℕ) (hk : 0 < k)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcard : ∀ x ∈ C, (fiber S.X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, StrictMono fun j : Fin k => (s j x) (Fin.last m)) :
    SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)} := by
  obtain ⟨mc, Cc, hCc⟩ := hCpf
  refine ⟨ocR p m mc k, ocW p m mc k Cc S.X hk, ?_⟩
  exact Set.Subset.antisymm
    (ocW_proj_superset Cc S.X C hCc hk s hsub hlvl)
    (ocW_proj_subset Cc S.X C hCc hk s hsub hcard)

end Work.WilE7.BelowAux
