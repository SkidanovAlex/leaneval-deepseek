import Mathlib
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.excisionTransfer
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.Serre.AttachCompress.Assemble
import Submission.Work.StemsB.pi_homeo_invariance
import Submission.Work.StemsB.PiMap
import Submission.Work.RatHurewicz.killFamily_subsingleton

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The inclusion of an attachment induces bijections on `π_{≤ n}`

Area **SERRE** (the C0/K1 step of the blueprint, in the "compression" form).  For a space `Y`, a
family of attaching maps `f : ι → C(S^{n+1}, Y)` and the space
`X = Work.RatHurewicz.attachCells n Y ι f` obtained from `Y` by gluing on `(n+2)`-cells along the
`f i`, the inclusion `attachIncl n Y ι f : Y → X` induces a **bijection** `π_k(Y) → π_k(X)` for
every `1 ≤ k ≤ n`: the attached cells are of dimension `n+2 > k`, so they are invisible to `π_k`.

## Route

Only the compression property of the pair `(X, range attachIncl)`, i.e. the statement that every
map of pairs `(I^d, ∂I^d) → (X, range attachIncl)` with `d ≤ n+1` is homotopic relative to `∂I^d`
into the range, is used.  It is available as `Work.Serre.AttachCompress.compression` (proved from
the general-position step `Work.AttachPush.exists_homotopy_avoids_cellOrigins` and the push-off
step `Work.RatHurewicz.exists_pushOff_homotopy`).

From the compression property, `Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel` gives
bijectivity of `π_j(↥(range attachIncl)) → π_j(X)` for `j + 2 ≤ n + 1` — this is a *direct*
argument, which unlike the long exact sequence of the pair (`Work.RatHurewicz.pair_les`, stated only
in degrees `≥ 3`) also covers the low degrees `j = 0, 1`, i.e. `π₁` and `π₂`, which are exactly the
cases the present statement needs at the top of the range (`k = 1, 2`).

`Work.RatHurewicz.rangeHomeo` identifies `Y` with `↥(range attachIncl)`, and a homeomorphism
induces bijections on homotopy groups (`Work.Serre.bijective_πmap_of_comp_eq_id_gen`, the
general-degree form of `Work.Serre.bijective_piMap_of_comp_eq_id`); composing the two bijections
along `setIncl (range attachIncl) ∘ rangeHomeo = attachIncl` gives the claim.
-/

open scoped Topology

namespace Work.Serre

/-- **`πmap` of a map admitting a two-sided inverse on the nose is bijective**, in every degree.
This is the general-degree form of `Work.Serre.bijective_piMap_of_comp_eq_id` (`π₁`): for
`f : C(X,Y)` and `g : C(Y,X)` with `g ∘ f = id` and `f ∘ g = id`, the induced maps on `π_{j+1}` are
mutually inverse up to the transport of the base point, so `πmap f j x` is bijective. -/
theorem bijective_πmap_of_comp_eq_id_gen {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (h1 : g.comp f = ContinuousMap.id X)
    (h2 : f.comp g = ContinuousMap.id Y) (j : ℕ) (x : X) :
    Function.Bijective (Work.StemsB.πmap f j x) := by
  let h1' : g (f x) = x := congrArg (fun k : C(X, X) => k x) h1
  let h2' : f (g (f x)) = f x := congrArg (fun k : C(Y, Y) => k (f x)) h2
  let cast1 : HomotopyGroup (Fin (j + 1)) X (g (f x)) ≃*
      HomotopyGroup (Fin (j + 1)) X x :=
    Work.StemsB.homotopyGroupCast h1' j
  let cast2 : HomotopyGroup (Fin (j + 1)) Y (f (g (f x))) ≃*
      HomotopyGroup (Fin (j + 1)) Y (f x) :=
    Work.StemsB.homotopyGroupCast h2' j
  have key1 : ∀ a : HomotopyGroup (Fin (j + 1)) X x,
      cast1 (Work.StemsB.πmap g j (f x) (Work.StemsB.πmap f j x a)) = a := by
    intro a
    show Work.StemsB.homotopyGroupCast h1' j
      (Work.StemsB.πmap g j (f x) (Work.StemsB.πmap f j x a)) = a
    rw [← Work.StemsB.πmap_comp_apply f g j x a]
    exact (Work.StemsB.πmap_congr h1 j x a).trans (Work.StemsB.πmap_id_apply j x a)
  have key2 : ∀ b : HomotopyGroup (Fin (j + 1)) Y (f x),
      cast2 (Work.StemsB.πmap f j (g (f x)) (Work.StemsB.πmap g j (f x) b)) = b := by
    intro b
    show Work.StemsB.homotopyGroupCast h2' j
      (Work.StemsB.πmap f j (g (f x)) (Work.StemsB.πmap g j (f x) b)) = b
    rw [← Work.StemsB.πmap_comp_apply g f j (f x) b]
    exact (Work.StemsB.πmap_congr h2 j (f x) b).trans (Work.StemsB.πmap_id_apply j (f x) b)
  have hginj : Function.Injective (Work.StemsB.πmap g j (f x)) := by
    intro b₁ b₂ hb
    rw [← key2 b₁, ← key2 b₂, hb]
  have key1' : ∀ a : HomotopyGroup (Fin (j + 1)) X x,
      Work.StemsB.πmap g j (f x) (Work.StemsB.πmap f j x a) = cast1.symm a := by
    intro a
    exact cast1.injective (by rw [key1 a, MulEquiv.apply_symm_apply])
  have hfinj : Function.Injective (Work.StemsB.πmap f j x) := by
    intro a₁ a₂ ha
    rw [← key1 a₁, ← key1 a₂, ha]
  refine ⟨hfinj, fun b => ⟨cast1 (Work.StemsB.πmap g j (f x) b), ?_⟩⟩
  apply hginj
  rw [key1', MulEquiv.symm_apply_apply]

/-- **Attaching `(n+2)`-cells does not change `π_{≤ n}`.**  The inclusion
`attachIncl n Y ι f : Y → attachCells n Y ι f` induces a bijection on `π_k` for every `1 ≤ k ≤ n`.
(For `k ≤ n - 1` this also follows from the long exact sequence of the pair; the compression form
used here additionally covers `k = 1, 2`, where the pair sequence is a sequence of pointed sets.) -/
theorem attachIncl_piMap_bijective_of_compress (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (y₀ : Y) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    Function.Bijective (Work.StemsB.πmap (Work.RatHurewicz.attachIncl n Y ι f) (k - 1) y₀) := by
  have hcomp : ∀ d, d ≤ n + 1 → Work.RatHurewicz.CompressRel
      (Work.RatHurewicz.attachCells n Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl n Y ι f)) d :=
    Work.Serre.AttachCompress.compression n Y ι f
  let eC : C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f))) :=
    ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f), (Work.RatHurewicz.rangeHomeo n Y ι f).continuous⟩
  let eI : C(↥(Set.range (Work.RatHurewicz.attachIncl n Y ι f)), Y) :=
    ⟨⇑(Work.RatHurewicz.rangeHomeo n Y ι f).symm,
      (Work.RatHurewicz.rangeHomeo n Y ι f).symm.continuous⟩
  have hbijA : Function.Bijective (Work.StemsB.πmap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
      (k - 1) (eC y₀)) :=
    Work.RatHurewicz.bijective_πmap_setIncl_of_compressRel (eC y₀) (n + 1) hcomp (k - 1)
      (by omega)
  have hbijE : Function.Bijective (Work.StemsB.πmap eC (k - 1) y₀) :=
    bijective_πmap_of_comp_eq_id_gen eC eI (by ext y; simp [eC, eI])
      (by ext p; simp [eC, eI]) (k - 1) y₀
  have hcompmap :
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f))).comp eC
        = Work.RatHurewicz.attachIncl n Y ι f := by
    ext y
    rfl
  let F : HomotopyGroup (Fin (k - 1 + 1)) Y y₀ →
      HomotopyGroup (Fin (k - 1 + 1)) (Work.RatHurewicz.attachCells n Y ι f)
        (Work.RatHurewicz.attachIncl n Y ι f y₀) :=
    fun a => Work.StemsB.πmap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
      (k - 1) (eC y₀) (Work.StemsB.πmap eC (k - 1) y₀ a)
  let cast : HomotopyGroup (Fin (k - 1 + 1)) (Work.RatHurewicz.attachCells n Y ι f)
        (Work.RatHurewicz.attachIncl n Y ι f y₀) ≃*
      HomotopyGroup (Fin (k - 1 + 1)) (Work.RatHurewicz.attachCells n Y ι f)
        (Work.RatHurewicz.attachIncl n Y ι f y₀) :=
    Work.StemsB.homotopyGroupCast
      (congrArg (fun k : C(Y, Work.RatHurewicz.attachCells n Y ι f) => k y₀) hcompmap) (k - 1)
  have hF : Function.Bijective F := hbijA.comp hbijE
  have key : ∀ a, Work.StemsB.πmap (Work.RatHurewicz.attachIncl n Y ι f) (k - 1) y₀ a
      = cast (F a) := by
    intro a
    show Work.StemsB.πmap (Work.RatHurewicz.attachIncl n Y ι f) (k - 1) y₀ a
      = Work.StemsB.homotopyGroupCast
          (congrArg (fun k : C(Y, Work.RatHurewicz.attachCells n Y ι f) => k y₀) hcompmap) (k - 1)
          (Work.StemsB.πmap
            (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
            (k - 1) (eC y₀) (Work.StemsB.πmap eC (k - 1) y₀ a))
    rw [← Work.StemsB.πmap_congr hcompmap (k - 1) y₀ a,
      ← Work.StemsB.πmap_comp_apply eC
        (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl n Y ι f)))
        (k - 1) y₀ a]
  refine ⟨?_, ?_⟩
  · intro a₁ a₂ h
    have h₁ := key a₁
    have h₂ := key a₂
    rw [h₁, h₂] at h
    exact hF.1 (cast.injective h)
  · intro b
    obtain ⟨a, ha⟩ := hF.2 (cast.symm b)
    exact ⟨a, by rw [key a, ha, MulEquiv.apply_symm_apply]⟩

end Work.Serre
