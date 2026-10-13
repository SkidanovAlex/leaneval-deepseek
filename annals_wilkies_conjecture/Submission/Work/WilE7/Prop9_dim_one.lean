import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.DimOneCells
import Submission.Work.WilE7.star_algebra
import Submission.Work.WilE7.subPf_algebra
import Submission.Work.WilE7.poly_embed
import Submission.Work.WilE7.DimOneCellsStar
import Submission.Work.WilE7.DimOneCellsCyl
import Submission.Work.WilE7.DimOneCellsCompat
import Submission.Work.WilE7.DimOneCellsPoly

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-!
# BV Proposition 9 in dimension one

This file proves the statement `Work.WilE7.Prop9_dim_one`: BV Proposition 9 for `n = 1`,
assuming the component bound `E2_components` (`hE2`) for semi-Pfaffian sets.

The argument is the one-dimensional shortcut of the paper: for each `*`-set `π_i` (the image
of `X i` under `projFirst 1 m`) the hypothesis `hE2` bounds the number of connected components
of `X i` — hence also the number of connected components of `π_i ⊆ ℝ`, each of which is an
interval.  Cutting `[-1,1]` at the end points of all those intervals produces a family of
cells (their `Fin`-images: singletons and open intervals, `Work.WilE7.cuts`) which is a
cylindrical decomposition of `cubeC 1` and is compatible with every `π_i`; each cell is a
`SubPf`-set and a `*`-set of format `1` and degree `≤ 4`, and their number is polynomial in
`D` and `k`.

The pieces of the argument that are independent of the surrounding induction are delegated:

* `DimOneCellsStar`  : every cell is `Star 1 4 1` and `SubPf 1`;
* `DimOneCellsCyl`   : the cells form a cylindrical decomposition of `cubeC 1`;
* `DimOneCellsCompat`: the real-analysis ingredient of compatibility;
* `DimOneCellsPoly`  : the polynomial envelope for the number of cells.
-/

/-! ## First coordinates of a set in `ℝ^{1+m}` -/

/-- The set of first coordinates of a set `K ⊆ ℝ^{1+m}`.  This is the one-dimensional
inhabitant of the projection `projFirst 1 m '' K` (`Fin 1 → ℝ` is a line, not `ℝ`). -/
def projReal {m : ℕ} (K : Set (Fin (1 + m) → ℝ)) : Set ℝ :=
  (fun z => z (Fin.castAdd m (0 : Fin 1))) '' K

theorem mem_projReal {m : ℕ} {K : Set (Fin (1 + m) → ℝ)} {r : ℝ} :
    r ∈ projReal K ↔ ∃ z ∈ K, z (Fin.castAdd m (0 : Fin 1)) = r := Iff.rfl

theorem projReal_mono {m : ℕ} {K K' : Set (Fin (1 + m) → ℝ)} (h : K ⊆ K') :
    projReal K ⊆ projReal K' := Set.image_mono h

theorem projReal_nonempty {m : ℕ} {K : Set (Fin (1 + m) → ℝ)} (h : K.Nonempty) :
    (projReal K).Nonempty := h.image _

theorem projReal_subset_Icc {m : ℕ} {K : Set (Fin (1 + m) → ℝ)} (hK : K ⊆ cubeC (1 + m)) :
    projReal K ⊆ Set.Icc (-1 : ℝ) 1 := by
  rintro r ⟨z, hz, rfl⟩
  have h := hK hz (Fin.castAdd m (0 : Fin 1))
  rwa [abs_le] at h

theorem projReal_ordConnected {m : ℕ} {K : Set (Fin (1 + m) → ℝ)} (hK : IsPreconnected K) :
    (projReal K).OrdConnected := by
  have hcont : Continuous fun z : Fin (1 + m) → ℝ => z (Fin.castAdd m (0 : Fin 1)) :=
    continuous_apply _
  exact isPreconnected_iff_ordConnected.mp (hK.image _ hcont.continuousOn)

/-! ## Bounds on `sInf` and `sSup` inside `[-1,1]` -/

theorem abs_sInf_le_one {J : Set ℝ} (hJne : J.Nonempty) (hJsub : J ⊆ Set.Icc (-1 : ℝ) 1) :
    |sInf J| ≤ 1 := by
  have hbd : BddBelow J := ⟨-1, fun y hy => (hJsub hy).1⟩
  obtain ⟨y, hy⟩ := hJne
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact le_csInf ⟨y, hy⟩ fun z hz => (hJsub hz).1
  · exact le_trans (csInf_le hbd hy) (hJsub hy).2

theorem abs_sSup_le_one {J : Set ℝ} (hJne : J.Nonempty) (hJsub : J ⊆ Set.Icc (-1 : ℝ) 1) :
    |sSup J| ≤ 1 := by
  have hbu : BddAbove J := ⟨1, fun y hy => (hJsub hy).2⟩
  obtain ⟨y, hy⟩ := hJne
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact le_trans (hJsub hy).1 (le_csSup hbu hy)
  · exact csSup_le ⟨y, hy⟩ fun z hz => (hJsub hz).2

/-! ## The cut points associated with a family and a choice of hitting sets -/

/-- The cut points associated with a family `X` of semi-Pfaffian sets and a choice `s` of
finite hitting sets: the end points (`sInf`/`sSup` of the first coordinates) of the connected
components of `X i` through the points of `s i`. -/
def cutSet {k m : ℕ} (X : Fin k → SemiPf (1 + m)) (s : Fin k → Finset (Fin (1 + m) → ℝ)) :
    Finset ℝ :=
  (Finset.univ : Finset (Fin k)).biUnion fun i =>
    ((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))) ∪
      ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x)))

theorem mem_cutSet {k m : ℕ} {X : Fin k → SemiPf (1 + m)}
    {s : Fin k → Finset (Fin (1 + m) → ℝ)} {t : ℝ} :
    t ∈ cutSet X s ↔ ∃ (i : Fin k) (x : Fin (1 + m) → ℝ), x ∈ s i ∧
      (t = sInf (projReal (connectedComponentIn (X i).set x)) ∨
       t = sSup (projReal (connectedComponentIn (X i).set x))) := by
  unfold cutSet
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨i, -, ht⟩
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at ht
    rcases ht with ⟨x, hx, h⟩ | ⟨x, hx, h⟩
    · exact ⟨i, x, hx, Or.inl h.symm⟩
    · exact ⟨i, x, hx, Or.inr h.symm⟩
  · rintro ⟨i, x, hx, h | h⟩
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [Finset.mem_union]
      refine Or.inl ?_
      rw [h]
      exact Finset.mem_image_of_mem _ hx
    · refine ⟨i, Finset.mem_univ i, ?_⟩
      rw [Finset.mem_union]
      refine Or.inr ?_
      rw [h]
      exact Finset.mem_image_of_mem _ hx

theorem card_cutSet {k m : ℕ} (X : Fin k → SemiPf (1 + m))
    (s : Fin k → Finset (Fin (1 + m) → ℝ)) :
    (cutSet X s).card ≤ 2 * ∑ i, (s i).card := by
  have h1 : (cutSet X s).card
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)),
          ((((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))) ∪
            ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x)))).card) := by
    unfold cutSet
    exact Finset.card_biUnion_le
  have h2 : ∀ i : Fin k,
      (((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))) ∪
        ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x)))).card
        ≤ 2 * (s i).card := by
    intro i
    refine le_trans (Finset.card_union_le _ _) ?_
    have h3 : ((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))).card
        ≤ (s i).card := Finset.card_image_le
    have h4 : ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x))).card
        ≤ (s i).card := Finset.card_image_le
    omega
  calc (cutSet X s).card
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin k)),
          ((((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))) ∪
            ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x)))).card) := h1
    _ = ∑ i : Fin k,
          ((((s i).image fun x => sInf (projReal (connectedComponentIn (X i).set x))) ∪
            ((s i).image fun x => sSup (projReal (connectedComponentIn (X i).set x)))).card) := by
        simp
    _ ≤ ∑ i : Fin k, 2 * (s i).card := Finset.sum_le_sum fun i _ => h2 i
    _ = 2 * ∑ i : Fin k, (s i).card := (Finset.mul_sum _ _ _).symm

/-! ## Monotonicity of evaluation of a `ℕ`-polynomial -/

theorem eval_mono {p : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval_add, Polynomial.eval_add]; exact Nat.add_le_add hp hq
  | monomial n c =>
      rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left h n)

/-! ## Compatibility: an open cell meeting the projection is contained in it -/

/-- If an open interval `(a,b)` bounded by consecutive cut points meets the projection of a
semi-Pfaffian set `Y` (in the sense of one-dimensional cell membership), then `(a,b)` is
contained in that projection.

The proof takes a point `y` of the intersection, transports it to a connected component of
`Y` (using the hitting property `hhit`), and applies the real-analysis lemma
`DimOneCellsCompat` to the first coordinates of that component. -/
theorem compat_interval {m : ℕ} {Y : SemiPf (1 + m)} {sY : Finset (Fin (1 + m) → ℝ)}
    (hhit : ∀ x ∈ Y.set, ∃ y ∈ sY, connectedComponentIn Y.set x = connectedComponentIn Y.set y)
    {U : Finset ℝ} {a b : ℝ} (hab : a < b) (hnb : ∀ u ∈ U, ¬ (a < u ∧ u < b))
    (hUcut : ∀ x ∈ sY, sInf (projReal (connectedComponentIn Y.set x)) ∈ U ∧
      sSup (projReal (connectedComponentIn Y.set x)) ∈ U)
    (hmeet : (cellIoo a b ∩ projFirst 1 m '' Y.set).Nonempty) :
    cellIoo a b ⊆ projFirst 1 m '' Y.set := by
  obtain ⟨y, hyκ, hyπ⟩ := hmeet
  obtain ⟨z, hzY, hzy⟩ := hyπ
  obtain ⟨x₀, hx₀s, hcomp⟩ := hhit z hzY
  have hzmem : z ∈ connectedComponentIn Y.set x₀ := by
    have h := mem_connectedComponentIn hzY
    rwa [hcomp] at h
  have hJne : (projReal (connectedComponentIn Y.set x₀)).Nonempty :=
    ⟨z (Fin.castAdd m (0 : Fin 1)), z, hzmem, rfl⟩
  have hJsub : projReal (connectedComponentIn Y.set x₀) ⊆ Set.Icc (-1 : ℝ) 1 :=
    projReal_subset_Icc fun w hw => Work.WilE8.SemiPf.set_subset_cube Y (connectedComponentIn_subset _ _ hw)
  have hJord : (projReal (connectedComponentIn Y.set x₀)).OrdConnected :=
    projReal_ordConnected (isPreconnected_connectedComponentIn (x := x₀) (F := Y.set))
  have hy0 : y 0 ∈ projReal (connectedComponentIn Y.set x₀) := by
    have hyz : y 0 = z (Fin.castAdd m (0 : Fin 1)) := by rw [← hzy]; rfl
    rw [hyz]
    exact ⟨z, hzmem, rfl⟩
  have hmeetJ : ∃ r, a < r ∧ r < b ∧ r ∈ projReal (connectedComponentIn Y.set x₀) :=
    ⟨y 0, hyκ.1, hyκ.2, hy0⟩
  have hsub := DimOneCellsCompat hab hnb hJsub hJord hJne
    (hUcut x₀ hx₀s).1 (hUcut x₀ hx₀s).2 hmeetJ
  intro x hx
  have hxJ : x 0 ∈ projReal (connectedComponentIn Y.set x₀) := hsub ⟨hx.1, hx.2⟩
  obtain ⟨z', hz', hz'0⟩ := hxJ
  refine ⟨z', connectedComponentIn_subset _ _ hz', ?_⟩
  funext i
  rw [Fin.eq_zero i]
  exact hz'0

/-! ## The main theorem -/

theorem Prop9_dim_one
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (F : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
      ∀ (D k m : ℕ) (X : Fin k → WilkiesDesign.E.SemiPf (1 + m)),
        (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
        ∃ C : Finset (Set (Fin 1 → ℝ)),
          WilkiesDesign.E.IsCylDecompOn 1 (WilkiesDesign.E.cubeC 1) C ∧
          (∀ i, ∀ κ ∈ C, κ ⊆ WilkiesDesign.E.projFirst 1 m '' (X i).set ∨
            Disjoint κ (WilkiesDesign.E.projFirst 1 m '' (X i).set)) ∧
          C.card ≤ MvPolynomial.eval ![D, k] b ∧
          ∀ κ ∈ C, WilkiesDesign.E.Star a (c.eval D) 1 κ ∧ WilkiesDesign.E.SubPf 1 κ := by
  obtain ⟨p, hp⟩ := hE2 F
  obtain ⟨b, hb⟩ := DimOneCellsPoly p
  refine ⟨1, b, Polynomial.C 4, ?_⟩
  intro D k m X hX
  choose s hs using fun i => hp (1 + m) (X i) (hX i).1
  -- the cut points
  let U : Finset ℝ := insert (-1) (insert 1 (cutSet X s))
  have hcut : ∀ (i : Fin k) (x : Fin (1 + m) → ℝ), x ∈ s i →
      sInf (projReal (connectedComponentIn (X i).set x)) ∈ U ∧
      sSup (projReal (connectedComponentIn (X i).set x)) ∈ U := by
    intro i x hx
    have h1 : sInf (projReal (connectedComponentIn (X i).set x)) ∈ cutSet X s :=
      mem_cutSet.mpr ⟨i, x, hx, Or.inl rfl⟩
    have h2 : sSup (projReal (connectedComponentIn (X i).set x)) ∈ cutSet X s :=
      mem_cutSet.mpr ⟨i, x, hx, Or.inr rfl⟩
    refine ⟨?_, ?_⟩
    · change _ ∈ insert (-1) (insert 1 (cutSet X s))
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h1)
    · change _ ∈ insert (-1) (insert 1 (cutSet X s))
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h2)
  have hneg : (-1 : ℝ) ∈ U := by
    change (-1 : ℝ) ∈ insert (-1) (insert 1 (cutSet X s))
    exact Finset.mem_insert_self _ _
  have hpos : (1 : ℝ) ∈ U := by
    change (1 : ℝ) ∈ insert (-1) (insert 1 (cutSet X s))
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hUsub : ∀ t ∈ U, |t| ≤ 1 := by
    intro t ht
    change t ∈ insert (-1) (insert 1 (cutSet X s)) at ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · norm_num
    rcases Finset.mem_insert.mp ht with rfl | ht
    · norm_num
    obtain ⟨i, x, hx, h | h⟩ := mem_cutSet.mp ht
    · rw [h]
      exact abs_sInf_le_one
        (projReal_nonempty ⟨x, mem_connectedComponentIn ((hs i).2.1 hx)⟩)
        (projReal_subset_Icc fun w hw =>
          Work.WilE8.SemiPf.set_subset_cube (X i) (connectedComponentIn_subset _ _ hw))
    · rw [h]
      exact abs_sSup_le_one
        (projReal_nonempty ⟨x, mem_connectedComponentIn ((hs i).2.1 hx)⟩)
        (projReal_subset_Icc fun w hw =>
          Work.WilE8.SemiPf.set_subset_cube (X i) (connectedComponentIn_subset _ _ hw))
  refine ⟨cuts U, DimOneCellsCyl U hneg hpos hUsub, ?_, ?_, ?_⟩
  · -- compatibility with each projection
    intro i κ hκ
    rcases mem_cuts.mp hκ with ⟨t, ht, rfl⟩ | ⟨a₀, ha₀, b₀, hb₀, hab, hnb, rfl⟩
    · by_cases hy : pt1 t ∈ projFirst 1 m '' (X i).set
      · exact Or.inl fun x hx => by rw [mem_cellPt] at hx; rwa [hx]
      · refine Or.inr ?_
        rw [Set.disjoint_left]
        intro x hx hx'
        rw [mem_cellPt] at hx
        rw [hx] at hx'
        exact hy hx'
    · by_cases hne : (cellIoo a₀ b₀ ∩ projFirst 1 m '' (X i).set).Nonempty
      · exact Or.inl (compat_interval (Y := X i) (sY := s i) (hs i).2.2
          hab hnb (fun x hx => hcut i x hx) hne)
      · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr
          (Set.not_nonempty_iff_eq_empty.mp hne))
  · -- cardinality of the decomposition
    have hUcard : U.card ≤ (cutSet X s).card + 2 := by
      have h1 : U.card ≤ (insert (1 : ℝ) (cutSet X s)).card + 1 := by
        change (insert (-1) (insert 1 (cutSet X s))).card ≤ _
        exact Finset.card_insert_le _ _
      have h2 : (insert (1 : ℝ) (cutSet X s)).card ≤ (cutSet X s).card + 1 :=
        Finset.card_insert_le _ _
      omega
    have hsum : ∑ i : Fin k, (s i).card ≤ k * p.eval D := by
      have h1 : ∑ i : Fin k, (s i).card ≤ ∑ _i : Fin k, p.eval D :=
        Finset.sum_le_sum fun i _ => le_trans (hs i).1 (eval_mono (hX i).2)
      have h2 : (∑ _i : Fin k, p.eval D) = k * p.eval D := by
        simp [Finset.sum_const, Finset.card_univ]
      exact le_trans h1 (le_of_eq h2)
    have hTcard : (cutSet X s).card ≤ 2 * (k * p.eval D) := by
      refine le_trans (card_cutSet X s) ?_
      exact Nat.mul_le_mul_left 2 hsum
    have hbound : U.card + 1 ≤ 4 * (k * p.eval D) + 3 := by omega
    calc (cuts U).card ≤ (U.card + 1) ^ 2 := cuts_card U
      _ ≤ (4 * (k * p.eval D) + 3) ^ 2 := Nat.pow_le_pow_left hbound 2
      _ = MvPolynomial.eval ![D, k] b := (hb D k).symm
  · -- each cell is a `*`-set of format `1`, degree `4`, and sub-Pfaffian
    intro κ hκ
    have h := DimOneCellsStar U hUsub κ hκ
    simpa using h

end Work.WilE7
