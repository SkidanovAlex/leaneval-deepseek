import Mathlib
import Submission.Work.StemsB.rangeModelDefs
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModel.sphereExtend
import Submission.Work.Serre.attachIncl_piMap_bijective_of_compress
import Submission.Work.RatHurewicz.killFamily_subsingleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.StemsB

open scoped Topology Topology.Homotopy unitInterval
open Work.RatHurewicz

/-!
# The second structure map survives the killing step

Given a stage `s : StG Z z₀ n` of the model tower (so `π_{j+1}(s.g)` is bijective for `j ≤ n` and
`π_{n+2}(s.g)` is surjective) and a second map `c : C(s.Y, P)` whose `π_{m+1}` agrees with that of
`s.g` in kernel and is surjective (`SecondMapInv`), we extend `c` over the cells of
`Work.Serre.CWModel.killStep s` — the cells attached along representatives of the elements of the
kernel of `π_{n+2}(s.g)` — and keep the invariant.

The extension exists because every attaching class `α` of the killing step satisfies
`π_{n+2}(c) α = 1`:

* if `m + 1 = n + 2` this is `SecondMapInv` itself (the class lies in the kernel of `π_{n+2}(s.g)`);
* if `m + 1 < n + 2` this is the hypothesis `htriv` (`π_{n+2}(P)` is trivial).

The invariant at degree `m+1` for the extended data then follows: the inclusion of `s.Y` into the
killed space is surjective on `π_{m+1}` (it is bijective in the range `≤ n+1`, and surjective in
degree `n+2` — exactly the two cases of `m + 1 ≤ n + 2`), and `π_{m+1}` of both structure maps
factor through it.
-/

theorem secondMap_killStep {A : Type} [AddCommGroup A] {m : ℕ} {Z : Type} [TopologicalSpace Z]
    {z₀ : Z} {P : Type} [TopologicalSpace P] {p₀ : P} {n : ℕ} (hdeg : m + 1 ≤ n + 2)
    (s : Work.Serre.CWModel.StG Z z₀ n) (c : C(s.Y, P))
    (hc : SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) s.y₀ s.g c)
    (htriv : m + 1 < n + 2 → ∀ y : P, Subsingleton (HomotopyGroup (Fin (n + 2)) P y)) :
    ∃ c' : C((Work.Serre.CWModel.killStep s).Y, P),
      SecondMapInv (m := m) (Z := Z) (P := P) (p₀ := p₀) (Work.Serre.CWModel.killStep s).y₀
        (Work.Serre.CWModel.killStep s).g c' := by
  classical
  -- the index type of the killing step and its attaching maps
  let ι := {α : HomotopyGroup (Fin (n + 2)) s.Y s.y₀ //
    Work.Serre.piMapN s.g (n + 2) s.y₀ α = 1}
  let f : ι → C(cellSphere (n + 1), s.Y) := fun k => killFamily (n + 1) s.Y s.y₀ k.1
  let i' : C(s.Y, attachCells (n + 1) s.Y ι f) := attachIncl (n + 1) s.Y ι f
  -- every attached class dies in `P`
  have hk : ∀ k : ι, Work.Serre.piMapN c (n + 2) s.y₀ k.1 = 1 := by
    intro k
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · have hsub := htriv hlt (c s.y₀)
      exact hsub.elim _ _
    · cases heq
      exact (hc.2.1 k.1).mp k.2
  -- hence the attaching maps become null-homotopic after composition with `c`
  have hnull : ∀ k : ι, (c.comp (f k)).Homotopic
      (ContinuousMap.const (cellSphere (n + 1)) (c s.y₀)) := by
    intro k
    have hker : Work.Serre.piMapN c (n + 2) s.y₀ k.1 = 1 := hk k
    have hn : 1 ≤ n + 2 := by omega
    have hcube : GenLoop.Homotopic (Work.StemsB.genLoopMap c (n + 2) (Quotient.out (k.1)))
        (GenLoop.const (N := Fin (n + 2)) (X := P) (x := c s.y₀)) := by
      have h1 : (Quotient.mk _ (Work.StemsB.genLoopMap c (n + 2) (Quotient.out (k.1))) :
            HomotopyGroup (Fin (n + 2)) P (c s.y₀))
          = Quotient.mk (GenLoop.Homotopic.setoid (Fin (n + 2)) (c s.y₀))
              (GenLoop.const (N := Fin (n + 2)) (X := P) (x := c s.y₀)) := by
        rw [← Work.Serre.piMapN_apply_mk, Quotient.out_eq (k.1), hker]
        exact HomotopyGroup.one_def (N := Fin (n + 2)) (X := P) (x := c s.y₀)
      exact Quotient.exact h1
    have h2 := Work.Serre.CWModel.cubeLift_homotopic hn hcube
    rw [Work.RatHurewicz.cubeLift_genLoopMap, Work.Serre.CWModel.cubeLift_const] at h2
    exact h2
  -- the extensions over the attached cells
  let G : ι → C(cellDisk (n + 1), P) := fun k =>
    Classical.choose (Work.Serre.CWModel.sphereExtend (c.comp (f k))
      (hnull k).some.toContinuousMap (c s.y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
  have hG : ∀ (k : ι) (z : cellSphere (n + 1)),
      G k (cellSphereToDisk (n + 1) z) = c (f k z) := by
    intro k z
    have hspec := Classical.choose_spec (Work.Serre.CWModel.sphereExtend (c.comp (f k))
      (hnull k).some.toContinuousMap (c s.y₀)
      (hnull k).some.map_zero_left (hnull k).some.map_one_left)
    exact congrFun (congrArg DFunLike.coe hspec) z
  let c' : C(attachCells (n + 1) s.Y ι f, P) :=
    Work.Serre.CWModel.attachG (n + 1) s.Y ι f c G hG
  -- the inclusion is onto on `π_{m+1}`
  have hsurj : Function.Surjective (Work.Serre.piMapN i' (m + 1) s.y₀) := by
    rcases lt_or_eq_of_le hdeg with hlt | heq
    · have hbij : Function.Bijective (Work.StemsB.πmap i' m s.y₀) :=
        Work.Serre.attachIncl_piMap_bijective_of_compress (n + 1) s.Y ι f s.y₀ (m + 1)
          (by omega) (by omega)
      intro x
      obtain ⟨y, hy⟩ := hbij.2 x
      exact ⟨y, hy⟩
    · have hbase : Function.Surjective (Work.StemsB.πmap i' (n + 1) s.y₀) :=
        Work.RatHurewicz.surjective_πmap_attachIncl (n + 1) s.Y ι f s.y₀
      rw [heq]
      intro x
      obtain ⟨y, hy⟩ := hbase x
      exact ⟨y, hy⟩
  let gg := (Work.Serre.CWModel.killStep s).g
  let yy := (Work.Serre.CWModel.killStep s).y₀
  -- `π_{m+1}` of the two structure maps, read on the old part
  have hgx0 (y : HomotopyGroup (Fin (m + 1)) s.Y s.y₀) :
      Work.Serre.piMapN gg (m + 1) yy (Work.Serre.piMapN i' (m + 1) s.y₀ y)
        = Work.Serre.piMapN s.g (m + 1) s.y₀ y := by
    exact (Work.Serre.piMapN_comp i' gg (m + 1) s.y₀ y).symm
  have hcx0 (y : HomotopyGroup (Fin (m + 1)) s.Y s.y₀) :
      Work.Serre.piMapN c' (m + 1) yy (Work.Serre.piMapN i' (m + 1) s.y₀ y)
        = Work.Serre.piMapN c (m + 1) s.y₀ y :=
    (Work.Serre.piMapN_comp i' c' (m + 1) s.y₀ y).symm
  refine ⟨c', ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the base point
    exact (Work.Serre.CWModel.attachG_incl (n + 1) s.Y ι f c G hG s.y₀).trans hc.1
  · -- equality of kernels
    intro x
    obtain ⟨y, hy⟩ := hsurj x
    have hgx := hgx0 y
    have hcx := hcx0 y
    have eA : (Work.Serre.piMapN gg (m + 1) yy x = 1)
        ↔ (Work.Serre.piMapN s.g (m + 1) s.y₀ y = 1) := by
      rw [← hy]
      exact Iff.of_eq (congrArg (fun w => w = 1) hgx)
    have eB : (Work.Serre.piMapN c' (m + 1) yy x = 1)
        ↔ (Work.Serre.piMapN c (m + 1) s.y₀ y = 1) := by
      rw [← hy]
      exact Iff.of_eq (congrArg (fun w => w = 1) hcx)
    exact eA.trans ((hc.2.1 y).trans eB.symm)
  · -- surjectivity
    intro z
    obtain ⟨y, hy⟩ := hc.2.2 z
    refine ⟨Work.Serre.piMapN i' (m + 1) s.y₀ y, ?_⟩
    exact (hcx0 y).trans hy

end Work.StemsB
