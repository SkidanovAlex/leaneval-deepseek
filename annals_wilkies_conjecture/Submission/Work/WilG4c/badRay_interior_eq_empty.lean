import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG1.Cell.thin_union
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4c.BadRayDefs
import Submission.Work.WilG4c.Vpt_interior_eq_empty

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-!
## The bad-ray set of an `Ω`-set of empty interior

`badRay T u` is the set of points `x` whose segment `[u,x]` meets `T` in infinitely many points.
The theorem `badRay_interior_eq_empty` says that for `T` in a sharply o-minimal format with
`interior T = ∅`, this set is thin.  The proof is a cell argument on the *cone*

  `Vpt u T = {(x,t) | u + t • (x - u) ∈ T} ⊆ ℝ^{N+1}`,

whose `t`-fibre over `x` is exactly the parameter set appearing in `badRay`:

* `Vpt u T` is `Ω`-definable with bounds independent of `u`, `T` and `D`
  (module `Submission.Work.WilG4c.Vpt_mem`),
* `interior (Vpt u T) = ∅` whenever `interior T = ∅`
  (module `Submission.Work.WilG4c.Vpt_interior_eq_empty`),
* every *cell* with empty interior has a nowhere dense "infinite fibre" set
  (proved below as `cell_fibreInfinite_nowhereDense_aux`).

Given those, a sharp cylindrical decomposition of `ℝ^{N+1}` compatible with `Vpt u T` writes
`Vpt u T` as a finite union of cells of empty interior; the fibre of `Vpt u T` over `x` is the
union of the fibres of those cells, so if it is infinite some cell has an infinite fibre over
`x`, and the third input says that this can only happen on a nowhere dense set.  A finite union
of nowhere dense sets being nowhere dense, the bad-ray set is meager and hence thin.
-/

/-- A cell with empty interior has a nowhere dense set of points whose last-coordinate fibre is
infinite.  In a graph cell the fibre is a subsingleton, so the set is empty; in a band cell the
fibre is empty outside the base cell, and the base cell of a band of empty interior has empty
interior. -/
theorem cell_fibreInfinite_nowhereDense_aux {n : ℕ} {κ : Set (Fin (n + 1) → ℝ)}
    (hκ : WilkiesDesign.IsCell (n + 1) κ) (hint : interior κ = ∅) :
    IsNowhereDense {x : Fin n → ℝ |
      {t : ℝ | (Fin.snoc x t : Fin (n + 1) → ℝ) ∈ κ}.Infinite} := by
  classical
  cases hκ with
  | graph hC f hf =>
      rename_i Cbase
      have hempty : {x : Fin n → ℝ | {t : ℝ | (Fin.snoc x t : Fin (n + 1) → ℝ) ∈
          {z : Fin (n + 1) → ℝ | Fin.init z ∈ Cbase ∧ z (Fin.last n) = f (Fin.init z)}}.Infinite}
          = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro x hx
        refine hx ((Set.finite_singleton (f x)).subset ?_)
        intro t ht
        rw [Set.mem_singleton_iff]
        simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at ht
        exact ht.2
      rw [hempty]
      simp [IsNowhereDense]
  | band hC a b ha hb hab =>
      rename_i Cbase
      have hCin : interior Cbase = ∅ := by
        by_contra hne
        have hne' : (interior Cbase).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
        have h := Work.WilG1.Cell.interior_band_nonempty ha hb hab hne'
        rw [hint] at h
        exact h.ne_empty rfl
      have hCnwd : IsNowhereDense Cbase := Work.WilG1.Cell.isCell_isNowhereDense hC hCin
      have hsub : {x : Fin n → ℝ | {t : ℝ | (Fin.snoc x t : Fin (n + 1) → ℝ) ∈
          {z : Fin (n + 1) → ℝ | Fin.init z ∈ Cbase ∧
            a (Fin.init z) < (((z (Fin.last n) : ℝ)) : EReal) ∧
            (((z (Fin.last n) : ℝ)) : EReal) < b (Fin.init z)}}.Infinite} ⊆ Cbase := by
        intro x hx
        obtain ⟨t, ht⟩ := hx.nonempty
        simp only [Set.mem_ofPred_eq, Fin.init_snoc] at ht
        exact ht.1
      rw [IsNowhereDense] at hCnwd ⊢
      exact Set.eq_empty_of_subset_empty
        (le_trans (interior_mono (closure_mono hsub)) (le_of_eq hCnwd))

/-! ## The cone is an `Ω`-set

The map `(x,t) ↦ u + t • (x - u)` is not affine, but its graph is cut out by the *quadratic*
relations `y i = u i + t * (x i - u i)` (`i : Fin N`), each of total degree `2`, the constants
`u i` being absorbed into the coefficients.  Embedding `ℝ^{(N+1)+N}` as `(x,t)` followed by `y`,
intersecting the relation with the lift of `T` to the `y`-coordinates, and projecting out `y`
gives the cone, with format and degree depending only on `N`, `F0` and `D`. -/

/-- The index of the `i`-th `x`-coordinate in `ℝ^{(N+1)+N}` (first block, `x`-part). -/
def cIdxX (N : ℕ) (i : Fin N) : Fin ((N + 1) + N) := Fin.castAdd N i.castSucc

/-- The index of the parameter `t` in `ℝ^{(N+1)+N}` (last coordinate of the first block). -/
def cIdxT (N : ℕ) : Fin ((N + 1) + N) := Fin.castAdd N (Fin.last N)

/-- The index of the `i`-th `y`-coordinate in `ℝ^{(N+1)+N}` (second block). -/
def cIdxY (N : ℕ) (i : Fin N) : Fin ((N + 1) + N) := Fin.natAdd (N + 1) i

theorem append_cIdxX (N : ℕ) (w : Fin (N + 1) → ℝ) (y : Fin N → ℝ) (i : Fin N) :
    Fin.append w y (cIdxX N i) = Fin.init w i := by
  rw [cIdxX, Fin.append_left]
  rfl

theorem append_cIdxT (N : ℕ) (w : Fin (N + 1) → ℝ) (y : Fin N → ℝ) :
    Fin.append w y (cIdxT N) = w (Fin.last N) := by
  rw [cIdxT, Fin.append_left]

theorem append_cIdxY (N : ℕ) (w : Fin (N + 1) → ℝ) (y : Fin N → ℝ) (i : Fin N) :
    Fin.append w y (cIdxY N i) = y i := by
  rw [cIdxY, Fin.append_right]

/-- The relation `y i = u i + t * (x i - u i)` for all `i`, in `ℝ^{(N+1)+N}`. -/
def coneRel (N : ℕ) (u : Fin N → ℝ) : Set (Fin ((N + 1) + N) → ℝ) :=
  {z | ∀ i : Fin N, z (cIdxY N i) = u i + z (cIdxT N) * (z (cIdxX N i) - u i)}

/-- The degree-`2` polynomial encoding one coordinate of the relation. -/
def conePoly (N : ℕ) (u : Fin N → ℝ) (i : Fin N) : MvPolynomial (Fin ((N + 1) + N)) ℝ :=
  MvPolynomial.X (cIdxY N i) - MvPolynomial.C (u i) -
    MvPolynomial.X (cIdxT N) * (MvPolynomial.X (cIdxX N i) - MvPolynomial.C (u i))

theorem td_sub_C_le_gen {n : ℕ} (i : Fin n) (c : ℝ) :
    (MvPolynomial.X i - MvPolynomial.C c : MvPolynomial (Fin n) ℝ).totalDegree ≤ 1 := by
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (Work.WilG5.td_X_le i) (by norm_num)
  · exact le_trans (Work.WilG5.td_C_le c) (Nat.zero_le 1)

theorem conePoly_totalDegree (N : ℕ) (u : Fin N → ℝ) (i : Fin N) :
    (conePoly N u i).totalDegree ≤ 2 := by
  unfold conePoly
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le ?_ ?_)
  · exact le_trans (td_sub_C_le_gen (cIdxY N i) (u i)) (by norm_num)
  · calc (MvPolynomial.X (cIdxT N) *
          (MvPolynomial.X (cIdxX N i) - MvPolynomial.C (u i))).totalDegree
        ≤ (MvPolynomial.X (cIdxT N)).totalDegree +
          (MvPolynomial.X (cIdxX N i) - MvPolynomial.C (u i)).totalDegree :=
        Work.WilG5.td_mul_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.WilG5.td_X_le (cIdxT N))
          (td_sub_C_le_gen (cIdxX N i) (u i))
      _ ≤ 2 := by norm_num

/-- The relation set is `Ω`-definable: it is the intersection of `N` degree-`2` hypersurfaces. -/
theorem coneRel_mem (S : WilkiesDesign.SOMin) (N : ℕ) (u : Fin N → ℝ) :
    coneRel N u ∈ S.Ω (((N + 1) + N) + 1) (2 * N) ((N + 1) + N) := by
  have hzero : ∀ i : Fin N,
      {z : Fin ((N + 1) + N) → ℝ | MvPolynomial.eval z (conePoly N u i) = 0} ∈
        S.Ω ((N + 1) + N) 2 ((N + 1) + N) := by
    intro i
    exact Work.WilG5.mem_mono (S.hyp ((N + 1) + N) (conePoly N u i)) _ _ le_rfl
      (conePoly_totalDegree N u i)
  have hinter := S.inter (fun _ : Fin N => 2)
    (fun i : Fin N => {z : Fin ((N + 1) + N) → ℝ | MvPolynomial.eval z (conePoly N u i) = 0})
    hzero
  have hsum : (∑ _ : Fin N, 2) = 2 * N := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
  rw [hsum] at hinter
  have hset : (⋂ i : Fin N,
      {z : Fin ((N + 1) + N) → ℝ | MvPolynomial.eval z (conePoly N u i) = 0}) = coneRel N u := by
    ext z
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, coneRel]
    constructor
    · intro h i
      have hi : z (cIdxY N i) - u i - z (cIdxT N) * (z (cIdxX N i) - u i) = 0 := by
        have h' := h i
        simpa [conePoly, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
          MvPolynomial.eval_C] using h'
      linarith
    · intro h i
      have hi : z (cIdxY N i) = u i + z (cIdxT N) * (z (cIdxX N i) - u i) := h i
      simp only [conePoly, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
        MvPolynomial.eval_C]
      linarith
  rwa [hset] at hinter

/-- The cone `Vpt u T` is the projection of the relation set intersected with the lift of `T`
to the `y`-coordinates. -/
theorem projN_coneRel_inter_eq_Vpt (N : ℕ) (u : Fin N → ℝ) (T : Set (Fin N → ℝ)) :
    Work.WilG5.projN N (coneRel N u ∩ Work.WilG5.coordPre (cIdxY N) T) = Vpt u T := by
  ext w
  simp only [Work.WilG5.projN, Work.WilG5.coordPre, coneRel, Vpt, Set.mem_ofPred_eq,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨y, hyc, hypre⟩
    have hrel : ∀ i : Fin N, y i = u i + w (Fin.last N) * (Fin.init w i - u i) := by
      intro i
      have h := hyc i
      rw [append_cIdxY, append_cIdxT, append_cIdxX] at h
      exact h
    have hmem : (fun i : Fin N => u i + w (Fin.last N) * (Fin.init w i - u i)) ∈ T := by
      have hfun : (Fin.append w y) ∘ (cIdxY N) =
          fun i : Fin N => u i + w (Fin.last N) * (Fin.init w i - u i) := by
        funext i
        rw [Function.comp_apply, append_cIdxY, hrel i]
      rwa [hfun] at hypre
    have hpi : u + (w (Fin.last N)) • (Fin.init w - u) =
        fun i : Fin N => u i + w (Fin.last N) * (Fin.init w i - u i) := by
      funext i
      simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rwa [hpi]
  · intro hmem
    refine ⟨fun i => u i + w (Fin.last N) * (Fin.init w i - u i), ?_, ?_⟩
    · intro i
      rw [append_cIdxY, append_cIdxT, append_cIdxX]
    · have hfun : (Fin.append w (fun i : Fin N =>
            u i + w (Fin.last N) * (Fin.init w i - u i))) ∘ (cIdxY N) =
          fun i : Fin N => u i + w (Fin.last N) * (Fin.init w i - u i) := by
        funext i
        rw [Function.comp_apply, append_cIdxY]
      have hpi : u + (w (Fin.last N)) • (Fin.init w - u) =
          fun i : Fin N => u i + w (Fin.last N) * (Fin.init w i - u i) := by
        funext i
        simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hfun, ← hpi]
      exact hmem

/-- An upper bound for the format of the cone before the projection. -/
def coneFmt (F0 N : ℕ) : ℕ := F0 + 64 * (((N + 1) + N) + N) + 64 + (((N + 1) + N) + 1)

/-- The degree polynomial of the cone: the degree of the relation plus that of the lift. -/
def coneDeg (N : ℕ) : Polynomial ℕ :=
  Polynomial.C (2 * N) + (Polynomial.X + Polynomial.C (32 * (((N + 1) + N) + N) + 32))

/-- **The cone of an `Ω`-set is an `Ω`-set**, at format and degree depending only on `N`, `F0`
and `D`. -/
theorem vpt_mem_local (S : WilkiesDesign.SOMin) (F0 N : ℕ) :
    ∃ (A : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (u : Fin N → ℝ) (T : Set (Fin N → ℝ)),
      T ∈ S.Ω F0 D N → Vpt u T ∈ S.Ω A (b.eval D) (N + 1) := by
  refine ⟨coneFmt F0 N + 1 + N, coneDeg N, ?_⟩
  intro D u T hT
  have h1 : coneRel N u ∈ S.Ω (coneFmt F0 N) (2 * N) ((N + 1) + N) :=
    Work.WilG1.Omega.mono (coneRel_mem (S := S) N u)
      (by simp only [coneFmt]; omega) le_rfl
  have h2 : Work.WilG5.coordPre (cIdxY N) T ∈ S.Ω (coneFmt F0 N)
      (D + (32 * (((N + 1) + N) + N) + 32)) ((N + 1) + N) :=
    Work.WilG1.Omega.mono (Work.WilG5.coordPre_mem (S := S) (ι := cIdxY N) (A := T) hT)
      (by simp only [coneFmt]; omega) le_rfl
  have h1' : coneRel N u ∈ S.Ω (coneFmt F0 N)
      ((Polynomial.C (2 * N)).eval D) ((N + 1) + N) := by simpa using h1
  have h2' : Work.WilG5.coordPre (cIdxY N) T ∈ S.Ω (coneFmt F0 N)
      ((Polynomial.X + Polynomial.C (32 * (((N + 1) + N) + N) + 32)).eval D)
      ((N + 1) + N) := by simpa using h2
  have hW := Work.WilG1.Omega.inter₂ h1' h2'
  have hW' : coneRel N u ∩ Work.WilG5.coordPre (cIdxY N) T ∈ S.Ω (coneFmt F0 N + 1)
      ((coneDeg N).eval D) ((N + 1) + N) := by
    refine Work.WilG1.Omega.mono hW ?_ le_rfl
    rw [max_self]
  have hV := Work.WilG5.projN_mem (S := S) (n := N + 1) N (coneFmt F0 N + 1)
    ((coneDeg N).eval D) hW'
  rwa [projN_coneRel_inter_eq_Vpt N u T] at hV

/-- The main argument, from the three ingredients: an `Ω`-format bound `(A, b)` for the cone
`Vpt · ·`, thinness of the cone, and thinness of the infinite-fibre sets of a cell. -/
theorem badRay_interior_eq_empty_of (S : WilkiesDesign.SOMin)
    (hcd : WilkiesDesign.SOMin.SharpCD S) (N F0 A : ℕ) (b : Polynomial ℕ)
    (hVmem : ∀ (D : ℕ) (u : Fin N → ℝ) (T : Set (Fin N → ℝ)), T ∈ S.Ω F0 D N →
      Vpt u T ∈ S.Ω A (b.eval D) (N + 1))
    (hVint : ∀ (u : Fin N → ℝ) (T : Set (Fin N → ℝ)), interior T = ∅ →
      interior (Vpt u T) = ∅)
    (hcell : ∀ {n : ℕ} {κ : Set (Fin (n + 1) → ℝ)}, WilkiesDesign.IsCell (n + 1) κ →
      interior κ = ∅ →
      IsNowhereDense {x : Fin n → ℝ |
        {t : ℝ | (Fin.snoc x t : Fin (n + 1) → ℝ) ∈ κ}.Infinite}) :
    ∀ (D : ℕ) (T : Set (Fin N → ℝ)) (u : Fin N → ℝ),
      T ∈ S.Ω F0 D N → interior T = ∅ → interior (badRay T u) = ∅ := by
  intro D T u hT hint
  classical
  -- a sharp cylindrical decomposition of `ℝ^{N+1}` compatible with the cone `Vpt u T`
  obtain ⟨a, bm, c, H⟩ := hcd A (N + 1)
  obtain ⟨C, hCdec, hCsep, -, -⟩ :=
    H (b.eval D) 1 (fun _ => Vpt u T) (fun _ => hVmem D u T hT)
  set CV : Finset (Set (Fin (N + 1) → ℝ)) := C.filter (fun κ => κ ⊆ Vpt u T) with hCV
  -- the cone is the union of the cells it contains
  have hVeq : Vpt u T = ⋃₀ (CV : Set (Set (Fin (N + 1) → ℝ))) := by
    ext z
    constructor
    · intro hz
      obtain ⟨κ, hκC, hzκ⟩ := Work.WilG1.Cell.exists_mem_of_cylDecomp hCdec z
      have hsub : κ ⊆ Vpt u T := by
        rcases hCsep 0 κ hκC with h | hd
        · exact h
        · exact absurd hz (Set.disjoint_left.mp hd hzκ)
      exact Set.mem_sUnion.mpr ⟨κ, by rw [hCV]; exact Finset.mem_filter.mpr ⟨hκC, hsub⟩, hzκ⟩
    · rintro ⟨κ, hκ, hzκ⟩
      rw [hCV] at hκ
      exact (Finset.mem_filter.mp hκ).2 hzκ
  -- each cell of the decomposition contained in the cone has a nowhere dense infinite-fibre set
  have hpiece : ∀ κ ∈ CV, IsNowhereDense
      {x : Fin N → ℝ | {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ}.Infinite} := by
    intro κ hκ
    have hκf : κ ∈ C.filter (fun κ => κ ⊆ Vpt u T) := hCV ▸ hκ
    have hκC : κ ∈ C := (Finset.mem_filter.mp hκf).1
    have hsubV : κ ⊆ Vpt u T := (Finset.mem_filter.mp hκf).2
    have hintκ : interior κ = ∅ :=
      Set.eq_empty_of_subset_empty
        (by rw [← hVint u T hint]; exact interior_mono hsubV)
    exact hcell (Work.WilG1.Cell.isCell_of_mem_cylDecomp hCdec hκC) hintκ
  -- the bad-ray set is contained in the union of the infinite-fibre sets
  have hBsub : badRay T u ⊆ ⋃ κ ∈ CV,
      {x : Fin N → ℝ | {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ}.Infinite} := by
    intro x hx
    have hinf : {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ Vpt u T}.Infinite :=
      badRay_subset_fibre T u hx
    have hfibe : {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ Vpt u T} =
        ⋃ κ ∈ CV, {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ} := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro ht
        have hz : (Fin.snoc x t : Fin (N + 1) → ℝ) ∈
            ⋃₀ (CV : Set (Set (Fin (N + 1) → ℝ))) := by
          rw [← hVeq]; exact ht
        obtain ⟨κ, hκ, htκ⟩ := Set.mem_sUnion.mp hz
        exact ⟨κ, hκ, htκ⟩
      · rintro ⟨κ, hκ, htκ⟩
        have hz : (Fin.snoc x t : Fin (N + 1) → ℝ) ∈
            ⋃₀ (CV : Set (Set (Fin (N + 1) → ℝ))) :=
          Set.mem_sUnion.mpr ⟨κ, hκ, htκ⟩
        rwa [← hVeq] at hz
    rw [hfibe] at hinf
    by_contra hcon
    have hcon' : ∀ κ ∈ CV,
        ¬ ({t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ}.Infinite) := by
      intro κ hκ hκinf
      exact hcon (Set.mem_iUnion.mpr ⟨κ, Set.mem_iUnion.mpr ⟨hκ, hκinf⟩⟩)
    have hfin : (⋃ κ ∈ CV, {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ}).Finite :=
      Set.Finite.biUnion CV.finite_toSet (fun κ hκ => Set.not_infinite.mp (hcon' κ hκ))
    exact (Set.not_infinite.mpr hfin) hinf
  -- a finite union of nowhere dense sets is nowhere dense, and the bad-ray set sits inside it
  have hnw : IsNowhereDense (⋃ κ ∈ CV,
      {x : Fin N → ℝ | {t : ℝ | (Fin.snoc x t : Fin (N + 1) → ℝ) ∈ κ}.Infinite}) :=
    IsNowhereDense.biUnion hpiece
  exact Set.eq_empty_of_subset_empty (le_trans (interior_mono hBsub)
    (le_trans (interior_mono subset_closure) (le_of_eq hnw)))

theorem badRay_interior_eq_empty (S : WilkiesDesign.SOMin) (hcd : WilkiesDesign.SOMin.SharpCD S)
    (N F0 : ℕ) :
    ∀ (D : ℕ) (T : Set (Fin N → ℝ)) (u : Fin N → ℝ),
      T ∈ S.Ω F0 D N → interior T = ∅ →
      interior {x : Fin N → ℝ | {t : ℝ | t ∈ Set.Ioc (0 : ℝ) 1 ∧ u + t • (x - u) ∈ T}.Infinite} = ∅ := by
  obtain ⟨A, b, hVmem⟩ := vpt_mem_local S F0 N
  exact badRay_interior_eq_empty_of S hcd N F0 A b hVmem
    (fun u T hint => Vpt_interior_eq_empty u T hint)
    (fun hκ hint => cell_fibreInfinite_nowhereDense_aux hκ hint)

end Work.WilG4c
