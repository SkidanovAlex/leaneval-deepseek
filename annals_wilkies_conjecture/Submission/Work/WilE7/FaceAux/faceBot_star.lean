import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowPhi_mem
import Submission.Work.WilE7.BelowAux.belowPhi_continuous
import Submission.Work.WilE7.reindex_component
import Submission.Work.WilE7.star_proj
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.FaceAux.BotDefs
import Submission.Work.WilE7.FaceAux.botY1_component
import Submission.Work.WilE7.FaceAux.botPerm_proj

namespace Work.WilE7.FaceAux

/-! ## The bottom face as the image of the base -/

/-- `t ↦ (t, -1)`: the bottom face point over `t`. -/
def botSnoc {p : ℕ} (t : Fin p → ℝ) : Fin (p + 1) → ℝ :=
  Fin.snoc (α := fun _ => ℝ) t (-1)

@[simp] theorem botSnoc_apply_last {p : ℕ} (t : Fin p → ℝ) :
    botSnoc t (Fin.last p) = -1 :=
  Fin.snoc_last (α := fun _ => ℝ) (-1) t

@[simp] theorem init_botSnoc {p : ℕ} (t : Fin p → ℝ) : Fin.init (botSnoc t) = t :=
  Fin.init_snoc (α := fun _ => ℝ) (-1) t

/-- The degree budget `3 (D+1)`, as a polynomial in `D`. -/
theorem eval_three (D : ℕ) :
    (Polynomial.C 3 * Polynomial.X + Polynomial.C 3).eval D = 3 * (D + 1) := by
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The bottom face `{y | Fin.init y ∈ C ∧ y (Fin.last p) = -1}` is the image of `C` under
`t ↦ (t,-1)`. -/
theorem faceBot_eq_image {p : ℕ} (C : Set (Fin p → ℝ)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1} = botSnoc '' C := by
  ext y
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Fin.init y, h1, ?_⟩
    rw [botSnoc, ← h2]
    exact Fin.snoc_init_self y
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by rw [init_botSnoc]; exact ht, by rw [botSnoc_apply_last]⟩

theorem faceBot_star
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    ∃ (a : ℕ) (c : Polynomial ℕ), ∀ (D F : ℕ),
      S.X.fmt ≤ F → S.deg ≤ D → Z.fmt ≤ F → Z.deg ≤ D →
      WilkiesDesign.E.Star a (c.eval D) (p + 1)
        {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1} := by
  classical
  -- the base component, the pinned set and the coordinate permutation
  set compZ : Set (Fin (p + (m + 1)) → ℝ) := connectedComponentIn Z.set u₀ with hcompZ
  set e : Equiv.Perm (Fin (botK p m)) := botPerm p m with he
  set X1 : WilkiesDesign.E.SemiPf (botK p m) := botY1 Z with hX1
  set P : WilkiesDesign.E.StarPiece (p + 1) :=
    ⟨m + 1, Work.WilE7.SemiPf.reindex e X1, (Work.WilE7.pullHomeo e).symm (botPinPt u₀)⟩ with hP
  -- the component of the pinned set is the pinned image of the component of `Z`
  have hcomp : connectedComponentIn (Work.WilE7.SemiPf.reindex e X1).set
        ((Work.WilE7.pullHomeo e).symm (botPinPt u₀))
      = {y : Fin (botK p m) → ℝ | (fun i => y (e i)) ∈ botPinPt '' compZ} := by
    rw [Work.WilE7.sp_reindex_component e X1 (botPinPt u₀), hX1, botY1_component Z u₀ hu₀,
      ← hcompZ]
    ext y
    simp only [Set.mem_preimage, Work.WilE7.pullHomeo_apply, Set.mem_ofPred_eq]
  -- the projection of that component is the bottom face over `compZ`
  have hproj : WilkiesDesign.E.projFirst (p + 1) (m + 1) ''
        {y : Fin (botK p m) → ℝ | (fun i => y (e i)) ∈ botPinPt '' compZ}
      = (botSnoc ∘ WilkiesDesign.E.projFirst p (m + 1)) '' compZ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := hy
      refine ⟨x, hx, ?_⟩
      have hy' : y = fun j => botPinPt x (e.symm j) := by
        funext j
        have h := congrFun hxy (e.symm j)
        simp only [Equiv.apply_symm_apply] at h
        exact h.symm
      rw [hy', he]
      exact (botPerm_proj (p := p) (m := m) x).symm
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun j => botPinPt x (e.symm j), ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        have h2 : (fun i => (fun j => botPinPt x (e.symm j)) (e i)) = botPinPt x := by
          funext i
          simp
        rw [h2]
        exact ⟨x, hx, rfl⟩
      · rw [he]
        exact botPerm_proj (p := p) (m := m) x
  -- the set of the `*`-piece
  have hPimg : P.set = (botSnoc ∘ WilkiesDesign.E.projFirst p (m + 1)) '' compZ := by
    show WilkiesDesign.E.projFirst (p + 1) (m + 1) ''
        connectedComponentIn (Work.WilE7.SemiPf.reindex e X1).set
          ((Work.WilE7.pullHomeo e).symm (botPinPt u₀)) = _
    rw [hcomp, hproj]
  have hface : {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1} = botSnoc '' C :=
    faceBot_eq_image C
  have himage : botSnoc '' C = (botSnoc ∘ WilkiesDesign.E.projFirst p (m + 1)) '' compZ := by
    rw [hC, Set.image_image]
    rfl
  have hPset : P.set = {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ y (Fin.last p) = -1} := by
    rw [hPimg, ← himage, ← hface]
  refine ⟨Z.fmt + 1, Polynomial.C 3 * Polynomial.X + Polynomial.C 3, ?_⟩
  intro D F hSF hSD hZF hZD
  refine ⟨[P], ?_, ?_, ?_⟩
  · have hunion : (⋃ P' ∈ ([P] : List (WilkiesDesign.E.StarPiece (p + 1))), P'.set) = P.set := by
      ext x
      simp only [Set.mem_iUnion, List.mem_singleton, exists_prop, exists_eq_left]
    rw [← hPset, hunion]
  · intro P' hP'
    rw [List.mem_singleton] at hP'
    subst hP'
    show (Work.WilE7.SemiPf.reindex e X1).fmt ≤ Z.fmt + 1
    rw [show (Work.WilE7.SemiPf.reindex e X1).fmt = X1.fmt from rfl, hX1, botY1_fmt]
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [eval_three]
    show (Work.WilE7.SemiPf.reindex e X1).deg ≤ 3 * (D + 1)
    rw [Work.WilE7.sp_reindex_deg e X1, hX1]
    calc (botY1 Z).deg ≤ 3 * (Z.deg + 1) := botY1_deg Z
      _ ≤ 3 * (D + 1) := by omega

end Work.WilE7.FaceAux
