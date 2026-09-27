import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.locally_affine_of_convex

namespace Work.Engulf.E4Aux

open Set Metric PL

/-- **Whole-face `ψ`-affinity from a `SmoothChart`.**  Let `ψ` be a smoothing chart for `f` on the
subcomplex `L` of `Γ`, and let `T` be a family of faces of `Γ` inside `L` whose `f`-images lie in
the open `3/4`-cube of `ψ`.  If a face `s` of `Γ` is covered by the simplices of `T`, then `f` is
`ψ`-affine on `simp s` with chart coordinates in the *closed* `3/4`-cube. -/
theorem affine_on_face_of_smoothChart {n p N : ℕ} {M : Type*} [MetricSpace M]
    {X : Set M} {Γ : PL.Cx N} {L : Set (PL.E N)} {f : PL.E N → M} (ψ : PL.CubeChart n M)
    (hψ : Work.Engulf.SmoothChart p X Γ L f ψ)
    (T : Finset (Finset (PL.E N))) (hT : ∀ t ∈ T, t ∈ Γ.faces)
    (hTL : ∀ t ∈ T, PL.simp t ⊆ L)
    (hT3 : ∀ t ∈ T, f '' PL.simp t ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ))
    {s : Finset (PL.E N)} (hs : s ∈ Γ.faces) (hscov : PL.simp s ⊆ ⋃ t ∈ T, PL.simp t) :
    ∃ A : PL.E N →ᵃ[ℝ] PL.E n, (∀ x ∈ PL.simp s, A x ∈ PL.closedCube (3 / 4 : ℝ)) ∧
      Set.EqOn f (fun x => ψ.toFun (A x)) (PL.simp s) := by
  classical
  -- A simplex covered by finitely many faces of `Γ` lies in one of them.
  obtain ⟨t, htT, hst⟩ := Work.Engulf.simp_cover (K := Γ) hT hs hscov
  have htL : PL.simp t ⊆ L := hTL t htT
  have hsL : PL.simp s ⊆ L := Subset.trans hst htL
  -- The `f`-image of `simp s` lies in the *open* `3/4`-cube.
  have hfs3 : f '' PL.simp s ⊆ ψ.toFun '' PL.openCube (3 / 4 : ℝ) :=
    Subset.trans (image_mono hst) (hT3 t htT)
  have hfs : f '' PL.simp s ⊆ ψ.toFun '' PL.closedCube (3 / 4 : ℝ) :=
    Subset.trans hfs3 (image_mono (Work.Engulf.openCube_subset_closedCube (3 / 4 : ℝ)))
  have hsne : s.Nonempty := Γ.nonempty_of_mem_faces hs
  have hne : (PL.simp s).Nonempty := Work.Engulf.simp_nonempty hsne
  -- `ψ` is injective on the open unit cube.
  have hinj : ∀ x ∈ PL.openCube (n := n) 1, ∀ y ∈ PL.openCube (n := n) 1,
      ψ.toFun x = ψ.toFun y → x = y := by
    intro x hx y hy hxy
    have h := ψ.emb.injective
      (show (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨x, hx⟩ =
        (PL.openCube (n := n) 1).domRestrict ψ.toFun ⟨y, hy⟩ from hxy)
    exact congrArg Subtype.val h
  -- Local `ψ`-affinity of `f` at every point of `simp s`.
  have hloc : ∀ y ∈ PL.simp s, ∃ δ > 0, ∃ A : PL.E N →ᵃ[ℝ] PL.E n,
      ∀ z ∈ PL.simp s ∩ Metric.ball y δ, A z ∈ PL.openCube (n := n) 1 ∧
        f z = ψ.toFun (A z) := by
    intro y hy
    obtain ⟨δ, hδ, A, hA⟩ := hψ.2 t (hT t htT) htL y (hst hy) (hfs ⟨y, hy, rfl⟩)
    exact ⟨δ, hδ, A, fun z hz => hA z ⟨hst hz.1, hz.2⟩⟩
  -- Glue along the convex set `simp s`.
  obtain ⟨A, hA⟩ :=
    Work.Engulf.Auxi.locally_affine_of_convex ψ.toFun hinj (Work.Engulf.convex_simp s) hne f hloc
  refine ⟨A, fun x hx => ?_, fun x hx => (hA x hx).2⟩
  -- Coordinates land in the *closed* `3/4`-cube by injectivity of `ψ`.
  obtain ⟨b, hb, hbf⟩ := hfs3 ⟨x, hx, rfl⟩
  have hb1 : b ∈ PL.openCube (n := n) 1 := Work.Engulf.openCube_mono (by norm_num) hb
  have hAx : A x = b :=
    hinj (A x) (hA x hx).1 b hb1 (((hA x hx).2).symm.trans hbf.symm)
  rw [hAx]
  exact Work.Engulf.openCube_subset_closedCube (3 / 4 : ℝ) hb

end Work.Engulf.E4Aux
