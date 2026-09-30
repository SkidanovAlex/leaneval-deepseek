import Mathlib
import Submission.Work.StemsB.Fibrations

/-!
# Base change of a Serre fibration: the projection `Γ ×_B E → Γ`

`Work.StemsB.pullbackFst g p` is the first projection of the fibre product

  `Pullback g p = {(γ, e) : Γ × E // g γ = p e}`

to `Γ`, i.e. the **base change of `g` along `p`**.  The classical theorem (and the one needed by
the Serre spectral sequence machinery of this project, cf.
`Submission/Work/Serre/pullbackFst_piMapN_bijective.lean`) is:

> if `p : E → B` is a Serre fibration, then so is the projection `Γ ×_B E → Γ`, for *any*
> continuous `g : Γ → B`.

The proof is the standard one and is completely elementary at the level of the homotopy lifting
property.  Given `Z`, a lift `f : Z → Γ ×_B E` and a homotopy `H : I × Z → Γ` of its
`Γ`-coordinate, the `Γ`-coordinate of the lifted homotopy is `H` itself, and the `E`-coordinate is
obtained by applying the HLP of `p` to the base homotopy `g ∘ H : I × Z → B` and the initial
`E`-coordinate of `f`.  The two coordinates pair up at every time because `p` lifts *over* `g`.

Note the asymmetry with `Work.StemsB.hasHLP_pullback`, which is the mirror statement: there the
projection to `E'` is lifted using the HLP of `p` applied to the *other* factor.  Both statements
are instances of the same pullback-square argument; here the HLP of `p` is used to lift the
homotopy whose base is `B`.
-/

open scoped Topology unitInterval

namespace Work.Serre.Assembly

noncomputable section

/-- **Base change of the homotopy lifting property.**  If `p : E → B` has the HLP with respect to
`Z`, then so does the projection `Work.StemsB.pullbackFst g p : Γ ×_B E → Γ` of the fibre product
of `g` with `p`, for every `g : Γ → B`. -/
theorem hasHLP_pullbackFst {E B Γ Z : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] [TopologicalSpace Z] (g : C(Γ, B)) (p : C(E, B))
    (h : Work.StemsB.HasHLP p Z) : Work.StemsB.HasHLP (Work.StemsB.pullbackFst g p) Z := by
  intro f b H
  -- the `E`-coordinate of the given lift, i.e. the second projection of the pullback
  let f₂ : C(Z, E) := (Work.StemsB.pullbackSnd g p).comp f
  -- the base homotopy `g ∘ H` is a homotopy in `B` out of `p ∘ f₂`
  have hK0 : ∀ z : Z, (g.comp H.toContinuousMap) (0, z) = (p.comp f₂) z := by
    intro z
    show g (H.toContinuousMap (0, z)) = p (f₂ z)
    have h1 : H.toContinuousMap (0, z) = ((Work.StemsB.pullbackFst g p).comp f) z :=
      H.map_zero_left z
    rw [h1]
    exact (f z).2
  have hK1 : ∀ z : Z, (g.comp H.toContinuousMap) (1, z) = (g.comp b) z := by
    intro z
    show g (H.toContinuousMap (1, z)) = g (b z)
    have h1 : H.toContinuousMap (1, z) = b z := H.map_one_left z
    rw [h1]
  let KH : (p.comp f₂).Homotopy (g.comp b) :=
    ContinuousMap.Homotopy.mk (g.comp H.toContinuousMap) hK0 hK1
  -- lift it through the fibration `p`, giving the `E`-coordinate of the lifted homotopy
  obtain ⟨GP, HG, hHG⟩ := h f₂ (g.comp b) KH
  have hKH : KH.toContinuousMap = g.comp H.toContinuousMap := rfl
  have hHG' : ∀ w : ↑I × Z, p (HG.toContinuousMap w) = g (H.toContinuousMap w) := by
    intro w
    have hw : p (HG.toContinuousMap w) = KH.toContinuousMap w := by
      have h' := congrArg (fun u : C(↑I × Z, B) => u w) hHG
      simpa only [ContinuousMap.comp_apply] using h'
    rw [hKH] at hw
    simpa only [ContinuousMap.comp_apply] using hw
  -- pair the two coordinates; they land in the fibre product at every time
  have hGcont : Continuous fun w : ↑I × Z =>
      (⟨(H.toContinuousMap w, HG.toContinuousMap w), (hHG' w).symm⟩ :
        Work.StemsB.Pullback g p) :=
    Continuous.subtype_mk
      (H.toContinuousMap.continuous_toFun.prodMk HG.toContinuousMap.continuous_toFun)
      (fun w => (hHG' w).symm)
  let Gg : C(↑I × Z, Work.StemsB.Pullback g p) :=
    ⟨fun w => ⟨(H.toContinuousMap w, HG.toContinuousMap w), (hHG' w).symm⟩, hGcont⟩
  -- the endpoint of the lifted homotopy lies in the fibre product over `b`
  have hgb : ∀ z : Z, g (b z) = p (GP z) := by
    intro z
    have h1 : HG.toContinuousMap (1, z) = GP z := HG.map_one_left z
    have h2 : H.toContinuousMap (1, z) = b z := H.map_one_left z
    have h3 : p (HG.toContinuousMap (1, z)) = g (H.toContinuousMap (1, z)) := hHG' (1, z)
    rw [h1, h2] at h3
    exact h3.symm
  have hgcont : Continuous fun z : Z =>
      (⟨(b z, GP z), hgb z⟩ : Work.StemsB.Pullback g p) :=
    Continuous.subtype_mk (b.continuous_toFun.prodMk GP.continuous_toFun) hgb
  let gp : C(Z, Work.StemsB.Pullback g p) :=
    ⟨fun z => ⟨(b z, GP z), hgb z⟩, hgcont⟩
  -- the lifted homotopy, from `f` to the endpoint lift
  have hm0 : ∀ z : Z, Gg (0, z) = f z := by
    intro z
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact H.map_zero_left z
    · exact HG.map_zero_left z
  have hm1 : ∀ z : Z, Gg (1, z) = gp z := by
    intro z
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · exact H.map_one_left z
    · exact HG.map_one_left z
  refine ⟨gp, ContinuousMap.Homotopy.mk Gg hm0 hm1, ?_⟩
  ext w
  rfl

/-- **The base change of a Serre fibration is a Serre fibration**: for any `g : Γ → B` and any
Serre fibration `p : E → B`, the projection `Work.StemsB.pullbackFst g p : Γ ×_B E → Γ` is again a
Serre fibration. -/
theorem pullbackFst_serre {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B]
    [TopologicalSpace E] (g : C(Γ, B)) (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) :
    Work.StemsB.IsSerreFibration (Work.StemsB.pullbackFst g p) :=
  fun n => hasHLP_pullbackFst g p (hp n)

end

end Work.Serre.Assembly
