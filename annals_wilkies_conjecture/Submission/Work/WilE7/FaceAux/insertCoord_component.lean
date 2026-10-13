import Mathlib
import Submission.Work.WilE7.FaceAux.InsertCoord
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE8.Star.CylDef

set_option autoImplicit false
noncomputable section

namespace Work.WilE7.FaceAux

open WilkiesDesign WilkiesDesign.E

/-- The pinned extension is *cylindrical* over the connected component: the component of the
pinned point in `insertCoord X t` is exactly the graph of the insertion `insCoord p q · t` over
the component of `u₀` in `X`.

Both directions are instances of `Work.WilE7.imageSubsetConnectedComponentIn`: the insertion is
a continuous section of the forgetting map `cylProj p q` (identified by `cylProj_insCoord`), and
on the pinned set the two maps are mutually inverse (`insCoord_cylProj`). -/
private theorem insertCoord_image_component {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q))
    (u₀ : Fin (p + q) → ℝ) (hu₀ : u₀ ∈ X.set) {t : ℝ} (ht : |t| ≤ 1) :
    (fun w : Fin (p + q) → ℝ => Work.WilE8.Star.insCoord p q w t) ''
        connectedComponentIn X.set u₀
      = connectedComponentIn (Work.WilE7.FaceAux.insertCoord X t).set
          (Work.WilE8.Star.insCoord p q u₀ t) := by
  classical
  set S := (Work.WilE7.FaceAux.insertCoord X t).set with hS
  set comp := connectedComponentIn X.set u₀ with hcomp
  -- the pinned set, described by the forgetting map
  have hset : S = {z : Fin (p + 1 + q) → ℝ |
      Work.WilE8.Star.cylProj p q z ∈ X.set ∧ z (Work.WilE7.FaceAux.newIdx p q) = t} := by
    rw [hS, Work.WilE7.FaceAux.insertCoord_set X ht]
    rfl
  have hins : Continuous (fun w : Fin (p + q) → ℝ => Work.WilE8.Star.insCoord p q w t) :=
    (Work.WilE8.Star.continuous_insCoord p q).comp (continuous_id.prodMk continuous_const)
  have hproj : Continuous (Work.WilE8.Star.cylProj p q) := Work.WilE8.Star.continuous_cylProj p q
  -- the insertion maps `X.set` into the pinned set
  have hmemS : ∀ x ∈ X.set, Work.WilE8.Star.insCoord p q x t ∈ S := by
    intro x hx
    rw [hset]
    refine ⟨?_, ?_⟩
    · change (fun i => Work.WilE8.Star.insCoord p q x t (Work.WilE8.skipInj p q i)) ∈ X.set
      rw [show (fun i => Work.WilE8.Star.insCoord p q x t (Work.WilE8.skipInj p q i)) = x
        from funext fun i => Work.WilE8.Star.insCoord_skipInj p q x t i]
      exact hx
    · change Work.WilE8.Star.insCoord p q x t (Fin.castAdd q (Fin.last p)) = t
      exact Work.WilE8.Star.insCoord_new p q x t
  -- the forgetting map sends the pinned set into `X.set`
  have hprojS : ∀ y ∈ S, Work.WilE8.Star.cylProj p q y ∈ X.set := by
    intro y hy
    rw [hset] at hy
    exact hy.1
  -- on the pinned set the insertion is a right inverse of the forgetting map
  have hsec : ∀ y ∈ S, Work.WilE8.Star.insCoord p q (Work.WilE8.Star.cylProj p q y) t = y := by
    intro y hy
    rw [hset] at hy
    have hy' : Work.WilE8.Star.newCoord p q y = t := by
      simpa only [Work.WilE8.Star.newCoord, Work.WilE7.FaceAux.newIdx] using hy.2
    rw [← hy']
    exact Work.WilE8.Star.insCoord_cylProj p q y
  refine Set.Subset.antisymm ?_ ?_
  · -- the component of `X` maps into the component of the pinned set
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact Work.WilE7.imageSubsetConnectedComponentIn isPreconnected_connectedComponentIn
      hins.continuousOn (mem_connectedComponentIn hu₀)
      (fun y hy => hmemS y (connectedComponentIn_subset X.set u₀ hy)) w hw
  · -- and the pinned component projects back into the component of `X`
    intro z hz
    have hzS : z ∈ S := connectedComponentIn_subset S _ hz
    have h1 : Work.WilE8.Star.cylProj p q z ∈
        connectedComponentIn X.set (Work.WilE8.Star.cylProj p q
          (Work.WilE8.Star.insCoord p q u₀ t)) :=
      Work.WilE7.imageSubsetConnectedComponentIn isPreconnected_connectedComponentIn
        hproj.continuousOn (mem_connectedComponentIn (hmemS u₀ hu₀))
        (fun y hy => hprojS y (connectedComponentIn_subset S _ hy)) z hz
    rw [Work.WilE8.Star.cylProj_insCoord p q u₀ t] at h1
    exact ⟨Work.WilE8.Star.cylProj p q z, h1, hsec z hzS⟩

theorem insertCoord_component {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q))
    (u₀ : Fin (p + q) → ℝ) (hu₀ : u₀ ∈ X.set) {t : ℝ} (ht : |t| ≤ 1) :
    WilkiesDesign.E.projFirst (p + 1) q ''
        connectedComponentIn (Work.WilE7.FaceAux.insertCoord X t).set
          (Work.WilE8.Star.insCoord p q u₀ t)
      = {y : Fin (p + 1) → ℝ |
          Fin.init y ∈ WilkiesDesign.E.projFirst p q ''
            connectedComponentIn X.set u₀ ∧
          y (Fin.last p) = t} := by
  classical
  -- the component of the pinned set is the insertion of the component of `X`
  rw [← insertCoord_image_component X u₀ hu₀ ht, Set.image_image]
  -- the projection of an inserted tuple is the initial part with `t` appended
  rw [show (fun x : Fin (p + q) → ℝ =>
        WilkiesDesign.E.projFirst (p + 1) q (Work.WilE8.Star.insCoord p q x t))
      = fun x => Fin.snoc (α := fun _ : Fin (p + 1) => ℝ)
          (WilkiesDesign.E.projFirst p q x) t from by
    funext x
    exact Work.WilE8.Star.projFirst_insCoord x t]
  -- appending `t` is a bijection onto the face at level `t`
  ext y
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨by simpa [Fin.init_snoc] using (show WilkiesDesign.E.projFirst p q c ∈
        WilkiesDesign.E.projFirst p q '' connectedComponentIn X.set u₀ from ⟨c, hc, rfl⟩),
      by simp⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨c, hc, hceq⟩ := h1
    refine ⟨c, hc, ?_⟩
    show Fin.snoc (α := fun _ : Fin (p + 1) => ℝ) (WilkiesDesign.E.projFirst p q c) t = y
    rw [hceq, ← h2]
    exact Fin.snoc_init_self y

end Work.WilE7.FaceAux
