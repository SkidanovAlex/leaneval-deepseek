/-
  `Work.WilE7.GraphCellAux.graphCellStar_star`: the graph cells of the `Star`/`SubPf`
  presentation are `*`-sets.

  Given a `Good` stratum `S : Stratum p (m+1)` with `S.j = m+1` whose part over the base cell
  `C = π_p (connectedComponentIn Z.set u₀)` is covered by the graphs of the continuous maps
  `s j : C → ℝ^{m+1}` (`Work.WilE7.sheetComponent` / `sheetAssembly`), the *graph cell*

  `Γ_j = {y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)}`

  is the projection of a connected component of a semi-Pfaffian set, with format and degree
  bounded uniformly in the format/degree bounds `F`, `D` of `S.X` and `Z`.

  The construction is the paper's fibre product: put `q = m+1`,
  `W = {(z₁,z₂) : z₁ ∈ Z.set, z₂ ∈ S.X.set, π_p z₁ = π_p z₂} ⊆ ℝ^{(p+q)+(p+q)}`
  (`Work.WilE7.fiberProdZ Z S.X`) and let `O` be the component of
  `w₀ = (u₀, (π_p u₀, s j (π_p u₀)))` in `W`.  `Work.WilE7.sheetComponent` says that along `O`
  the second factor lies on the graph of `s j` and that `O` covers `C`, and the base projection
  of any point of `O` lies in `C` (the auxiliary lemma below).  Hence the map

  `graphProj z = Fin.snoc (π_p z₁) ((π_q z₂) (Fin.last m))`

  maps `O` onto `Γ_j`, and a coordinate permutation (`graphProj_perm`) turns `graphProj` into the
  projection `projFirst (p+1) ·` of the reindexed fibre product — which is exactly the `*`-piece
  attached to `Γ_j`.
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.sheetComponent
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

set_option autoImplicit false
noncomputable section
open Classical
open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.GraphCellAux

/-! ## Auxiliary: the base projection of a point of the fibre-product component -/

theorem sheetProduct_base_mem {p q : ℕ} (S : WilkiesDesign.E.Stratum p q)
    (Z : WilkiesDesign.E.SemiPf (p + q)) (u₀ : Fin (p + q) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p q) (connectedComponentIn Z.set u₀))
    {k : ℕ} (s : Fin k → (Fin p → ℝ) → (Fin q → ℝ)) (j : Fin k) :
    ∀ z ∈ connectedComponentIn (Work.WilE7.sheetProduct p q Z S)
        (Work.WilE7.sheetProductPt u₀ s j),
      WilkiesDesign.E.projFirst p q
        (WilkiesDesign.E.projFirst (p + q) (p + q) z) ∈ C := by
  have _ := hu₀
  by_cases hw : Work.WilE7.sheetProductPt u₀ s j ∈ Work.WilE7.sheetProduct p q Z S
  · intro z hz
    have hmem : WilkiesDesign.E.projFirst (p + q) (p + q) z ∈
        connectedComponentIn Z.set u₀ := by
      have h := Work.WilE7.imageSubsetConnectedComponentIn
        (s := connectedComponentIn (Work.WilE7.sheetProduct p q Z S)
          (Work.WilE7.sheetProductPt u₀ s j))
        isPreconnected_connectedComponentIn
        (continuous_projFirst (p + q) (p + q)).continuousOn
        (x := Work.WilE7.sheetProductPt u₀ s j) (mem_connectedComponentIn hw)
        (F := Z.set) (fun y hy => (Work.WilE7.mem_sheetProduct.mp
          (connectedComponentIn_subset _ _ hy)).1) z hz
      rwa [Work.WilE7.projFirst_sheetProductPt] at h
    rw [hC]
    exact ⟨_, hmem, rfl⟩
  · intro z hz
    rw [connectedComponentIn_eq_empty hw] at hz
    exact absurd hz (by simp)

/-! ## Auxiliary: the coordinate permutation putting the graph coordinates first -/

theorem graphProj_perm (p m : ℕ) :
    ∃ e : Fin ((p + (m + 1)) + (p + (m + 1))) ≃ Fin ((p + 1) + ((p + (m + 1)) + m)),
      ∀ y : Fin ((p + 1) + ((p + (m + 1)) + m)) → ℝ,
        WilkiesDesign.E.projFirst (p + 1) ((p + (m + 1)) + m) y =
          Fin.snoc
            (WilkiesDesign.E.projFirst p (m + 1)
              (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) (fun i => y (e i))))
            ((WilkiesDesign.E.projSnd p (m + 1)
              (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) (fun i => y (e i))))
              (Fin.last m)) := by
  classical
  have hNK : (p + (m + 1)) + (p + (m + 1)) = (p + 1) + ((p + (m + 1)) + m) := by omega
  have hpK : p < (p + 1) + ((p + (m + 1)) + m) := by omega
  have hK1 : ((p + 1) + ((p + (m + 1)) + m)) - 1 < (p + 1) + ((p + (m + 1)) + m) := by
    omega
  set K := (p + 1) + ((p + (m + 1)) + m) with hK
  set σ : Equiv.Perm (Fin K) := Equiv.swap ⟨p, hpK⟩ ⟨K - 1, hK1⟩ with hσ
  set e : Fin ((p + (m + 1)) + (p + (m + 1))) ≃ Fin K :=
    (Work.WilE7.finEquiv hNK).trans σ with he
  refine ⟨e, ?_⟩
  -- the value of `e` is the value of the swapped coordinate
  have hev : ∀ x : Fin ((p + (m + 1)) + (p + (m + 1))),
      (e x).val = (σ (Work.WilE7.finEquiv hNK x)).val := fun x => rfl
  -- `e` fixes the base coordinates and moves the last fibre coordinate of the second factor to
  -- position `p`
  have hE1 : ∀ i : Fin p, e (Fin.castAdd (p + (m + 1)) (Fin.castAdd (m + 1) i))
      = Fin.castAdd ((p + (m + 1)) + m) (Fin.castSucc i) := by
    intro i
    apply Fin.ext
    rw [hev]
    have hxa : Work.WilE7.finEquiv hNK (Fin.castAdd (p + (m + 1)) (Fin.castAdd (m + 1) i))
        ≠ (⟨p, hpK⟩ : Fin K) := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Work.WilE7.finEquiv_apply_val, Fin.val_castAdd] at h2
      omega
    have hxb : Work.WilE7.finEquiv hNK (Fin.castAdd (p + (m + 1)) (Fin.castAdd (m + 1) i))
        ≠ (⟨K - 1, hK1⟩ : Fin K) := by
      intro h
      have h2 := congrArg Fin.val h
      simp only [Work.WilE7.finEquiv_apply_val, Fin.val_castAdd] at h2
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
    simp [Work.WilE7.finEquiv_apply_val, Fin.val_castAdd, Fin.val_castSucc]
  have hE2 : e (Fin.natAdd (p + (m + 1)) (Fin.natAdd p (Fin.last m)))
      = Fin.castAdd ((p + (m + 1)) + m) (Fin.last p) := by
    have hxb : Work.WilE7.finEquiv hNK (Fin.natAdd (p + (m + 1)) (Fin.natAdd p (Fin.last m)))
        = (⟨K - 1, hK1⟩ : Fin K) := by
      apply Fin.ext
      simp only [Work.WilE7.finEquiv_apply_val, Fin.val_natAdd, Fin.val_last]
      omega
    apply Fin.ext
    rw [hev, hxb, Equiv.swap_apply_right]
    simp [Fin.val_castAdd, Fin.val_last]
  intro y
  set z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ := fun i => y (e i) with hz
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · simp only [WilkiesDesign.E.projFirst]
    rw [Fin.snoc_castSucc, ← hE1 i']
    rfl
  · simp only [WilkiesDesign.E.projFirst, WilkiesDesign.E.projSnd]
    rw [Fin.snoc_last, ← hE2]

/-! ## Auxiliary: the graph-cell projection of the fibre product -/

/-- The graph-cell projection of the fibre product: the base coordinates (taken from the first
factor) together with the last fibre coordinate of the second factor. -/
def graphProj {p m : ℕ} (z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc
    (WilkiesDesign.E.projFirst p (m + 1)
      (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z))
    ((WilkiesDesign.E.projSnd p (m + 1)
      (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z)) (Fin.last m))

theorem graphProj_init {p m : ℕ} (z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) :
    Fin.init (graphProj z) = WilkiesDesign.E.projFirst p (m + 1)
      (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z) :=
  Fin.init_snoc _ _

theorem graphProj_last {p m : ℕ} (z : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) :
    graphProj z (Fin.last p) = (WilkiesDesign.E.projSnd p (m + 1)
      (WilkiesDesign.E.projSnd (p + (m + 1)) (p + (m + 1)) z)) (Fin.last m) :=
  Fin.snoc_last _ _

/-! ## The graph cell is a `*`-set -/

theorem graphCellStar_star
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1)) (hGood : S.Good) (hj : S.j = m + 1)
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hcov : ∀ z ∈ S.X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) = WilkiesDesign.E.projSnd p (m + 1) z)
    (j : Fin k) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := by
  classical
  obtain ⟨e, he⟩ := graphProj_perm p m
  obtain ⟨hsheet, hcover⟩ :=
    Work.WilE7.sheetComponent S hGood hj Z u₀ hu₀ C hC k s hcont hinj hsub hcov j
  have hbase : ∀ z ∈ connectedComponentIn (Work.WilE7.sheetProduct p (m + 1) Z S)
        (Work.WilE7.sheetProductPt u₀ s j),
      WilkiesDesign.E.projFirst p (m + 1)
        (WilkiesDesign.E.projFirst (p + (m + 1)) (p + (m + 1)) z) ∈ C :=
    sheetProduct_base_mem S Z u₀ hu₀ C hC s j
  set W : WilkiesDesign.E.SemiPf ((p + (m + 1)) + (p + (m + 1))) :=
    Work.WilE7.fiberProdZ Z S.X with hW
  set w₀ : Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ :=
    Work.WilE7.sheetProductPt u₀ s j with hw₀
  set O : Set (Fin ((p + (m + 1)) + (p + (m + 1))) → ℝ) :=
    connectedComponentIn (Work.WilE7.sheetProduct p (m + 1) Z S) w₀ with hO
  have hWset : W.set = Work.WilE7.sheetProduct p (m + 1) Z S := by
    rw [hW]
    exact Work.WilE7.fiberProdZ_set Z S.X
  -- the `*`-piece: the reindexed fibre product, based at the reindexed base point
  set P : WilkiesDesign.E.StarPiece (p + 1) :=
    ⟨(p + (m + 1)) + m, Work.WilE7.SemiPf.reindex e W,
      (Work.WilE7.pullHomeo e).symm w₀⟩ with hP
  have hkey : ∀ y : Fin ((p + 1) + ((p + (m + 1)) + m)) → ℝ,
      WilkiesDesign.E.projFirst (p + 1) ((p + (m + 1)) + m) y
        = graphProj (Work.WilE7.pullHomeo e y) := by
    intro y
    rw [he y, Work.WilE7.pullHomeo_apply]
    rfl
  -- the piece's set is the image of the component under `graphProj`
  have hPset : P.set = graphProj '' O := by
    have hcomp := Work.WilE7.sp_reindex_component e W w₀
    rw [hP]
    show WilkiesDesign.E.projFirst (p + 1) ((p + (m + 1)) + m) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e W).set
          ((Work.WilE7.pullHomeo e).symm w₀) = graphProj '' O
    rw [hcomp, hWset, ← hO]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨Work.WilE7.pullHomeo e y, hy, (hkey y).symm⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨(Work.WilE7.pullHomeo e).symm z, ?_, ?_⟩
      · rw [Set.mem_preimage, Homeomorph.apply_symm_apply]
        exact hz
      · rw [hkey, Homeomorph.apply_symm_apply]
  -- `graphProj` maps the component onto the graph cell
  have hG : graphProj '' O
      = {y : Fin (p + 1) → ℝ |
          Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzW : z ∈ Work.WilE7.sheetProduct p (m + 1) Z S :=
        connectedComponentIn_subset (Work.WilE7.sheetProduct p (m + 1) Z S) w₀ hz
      obtain ⟨-, -, hzdiag⟩ := Work.WilE7.mem_sheetProduct.mp hzW
      refine ⟨?_, ?_⟩
      · rw [graphProj_init]
        exact hbase z hz
      · rw [graphProj_last, graphProj_init, hsheet z hz, ← hzdiag]
    · rintro ⟨hinit, hlast⟩
      obtain ⟨z, hzO, hzx⟩ := hcover (Fin.init y) hinit
      have hzW : z ∈ Work.WilE7.sheetProduct p (m + 1) Z S :=
        connectedComponentIn_subset (Work.WilE7.sheetProduct p (m + 1) Z S) w₀ hzO
      obtain ⟨-, -, hzdiag⟩ := Work.WilE7.mem_sheetProduct.mp hzW
      refine ⟨z, hzO, ?_⟩
      have h1 : Fin.init (graphProj z) = Fin.init y := by
        rw [graphProj_init, hzdiag]
        exact hzx
      have h2 : graphProj z (Fin.last p) = y (Fin.last p) := by
        rw [graphProj_last, hsheet z hzO, hzx]
        exact hlast.symm
      calc graphProj z = Fin.snoc (Fin.init (graphProj z)) (graphProj z (Fin.last p)) :=
            (Fin.snoc_init_self (graphProj z)).symm
        _ = Fin.snoc (Fin.init y) (y (Fin.last p)) := by rw [h1, h2]
        _ = y := Fin.snoc_init_self y
  have hPG : P.set = {y : Fin (p + 1) → ℝ |
      Fin.init y ∈ C ∧ y (Fin.last p) = (s j (Fin.init y)) (Fin.last m)} := hPset.trans hG
  have _ := hCpf
  refine ⟨2 * max S.X.fmt Z.fmt,
    Polynomial.C (2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2), ?_⟩
  intro D F hSF hSD hZF hZD
  have hfmt : P.X.fmt ≤ 2 * max S.X.fmt Z.fmt := by
    rw [hP]
    show (Work.WilE7.SemiPf.reindex e W).fmt ≤ 2 * max S.X.fmt Z.fmt
    have hre : (Work.WilE7.SemiPf.reindex e W).fmt = W.fmt := by
      simp only [Work.WilE7.SemiPf.reindex, WilkiesDesign.E.SemiPf.fmt]
      omega
    rw [hre]
    exact Work.WilE7.fiberProdZ_fmt Z S.X (le_max_right _ _) (le_max_left _ _)
  have hdeg : P.X.deg ≤ 2 * (1 + max S.X.fmt Z.fmt) * (1 + (Z.deg + S.X.deg)) ^ 2 := by
    rw [hP]
    show (Work.WilE7.SemiPf.reindex e W).deg ≤ _
    rw [Work.WilE7.sp_reindex_deg]
    exact Work.WilE7.fiberProdZ_deg Z S.X (le_max_right _ _)
  refine ⟨[P], ?_, ?_, ?_⟩
  · have hsingle : (⋃ P' ∈ ([P] : List (WilkiesDesign.E.StarPiece (p + 1))), P'.set) = P.set := by
      ext x
      simp
    rw [hsingle, hPG]
  · intro P' hP'
    rw [List.mem_singleton] at hP'
    subst hP'
    exact hfmt
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      Polynomial.eval_C]
    exact hdeg

end Work.WilE7.GraphCellAux
