import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.CORE2A.c14_lift

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- **P5, the isomorphism step.**  With `E := E(Ĥ)`, `Z := Z(E)`, `SE := ⟨S, E⟩` and
`φ : SE → PGL₂(q)` the quotient of `Thm26bAutProp` (a) (kernel `Z`, `φ(E) = L₂(q)`), the induced
map `C_E(t)/Z → C_{L₂(q)}(φ t)` is a bijection; hence

  `kE B = |C_E(t) : Z(E)| = |C_{L₂(q)}(φ t)|`.

Crux (`c14_lift`): an `x ∈ E` whose image commutes with `φ t` can be adjusted by an element of
the odd kernel `Z = Z(E)` to an element centralizing `t` (`u = t` is an involution of `SE`);
this is the source of the surjectivity of `φ ↾ C_E(t) → C_{L₂(q)}(φ t)`.

(`ht : t ∈ E` is kept for compatibility with the requested signature but is not needed: only
`htSE : t ∈ SE`, the fact that `t` is an involution, and `φ(E) = L₂(q)`, `ker φ = Z(E)`,
`|Z(E)|` odd are used.) -/
theorem c14_kE_card (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} {p k : ℕ} [Fact p.Prime] (D : Work.GW2.PGLData B p k) (htSE : B.t ∈ Work.GW2.SE B) (ht : B.t ∈ Work.GW2.layerIn B.Hhat) :
    Work.GW2.kE B = Nat.card ↥(Work.GW2.Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨B.t, htSE⟩} : Set (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)))) := by
  let E : Subgroup G := Work.GW2.layerIn B.Hhat
  let Z : Subgroup G := Work.GW2.zE B
  let SE : Subgroup G := Work.GW2.SE B
  let M : Subgroup G := E ⊓ Subgroup.centralizer ({B.t} : Set G)
  let N : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) :=
    Work.GW2.Lsub p k ⊓ Subgroup.centralizer ({D.φ ⟨B.t, htSE⟩} : Set _)
  change Work.GW2.kE B = Nat.card ↥N
  -- `t` is an involution
  have ht2 : B.t * B.t = 1 := by
    have h := pow_orderOf_eq_one B.t
    rw [B.t_order] at h
    simpa [pow_two] using h
  -- the key subgroup equality: `φ(C_E(t)) = C_{L₂(q)}(φ t)`
  have hmap : (M.subgroupOf SE).map D.φ = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxM : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hx
      have hxE : (x : G) ∈ E := (Subgroup.mem_inf.mp hxM).1
      have hxC : (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) := (Subgroup.mem_inf.mp hxM).2
      rw [Subgroup.mem_inf]
      constructor
      · exact (D.mem_layer_iff x).mp hxE
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hcommG : (x : G) * B.t = B.t * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hxC
        have hcomm : x * ⟨B.t, htSE⟩ = ⟨B.t, htSE⟩ * x := Subtype.ext hcommG
        calc D.φ x * D.φ ⟨B.t, htSE⟩ = D.φ (x * ⟨B.t, htSE⟩) := (map_mul _ _ _).symm
          _ = D.φ (⟨B.t, htSE⟩ * x) := by rw [hcomm]
          _ = D.φ ⟨B.t, htSE⟩ * D.φ x := map_mul _ _ _
    · rintro ⟨hyL, hyC⟩
      obtain ⟨x, hφx⟩ := D.surj y
      have hxE : (x : G) ∈ E := (D.mem_layer_iff x).mpr (by rw [hφx]; exact hyL)
      have hc : D.φ x * D.φ ⟨B.t, htSE⟩ = D.φ ⟨B.t, htSE⟩ * D.φ x := by
        have hcy : y * D.φ ⟨B.t, htSE⟩ = D.φ ⟨B.t, htSE⟩ * y :=
          Subgroup.mem_centralizer_singleton_iff.mp hyC
        rw [hφx]; exact hcy
      obtain ⟨x', hx'E, hx'comm, hφx'⟩ :=
        Work.CORE2A.c14_lift T hFT hbc D htSE ht2 x hxE hc
      refine Subgroup.mem_map.mpr ⟨x', ?_, ?_⟩
      · rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_inf.mpr ⟨hx'E, Subgroup.mem_centralizer_singleton_iff.mpr hx'comm⟩
      · rw [hφx', hφx]
  have hMSE : M ≤ SE := inf_le_left.trans Work.CORE2A.layerIn_le_SE
  -- `|φ(C_E(t))| = |C_E(t) : Z(E)| = kE B`, by the first isomorphism theorem
  have hcard : Nat.card ↥((M.subgroupOf SE).map D.φ) = Z.relIndex M := by
    rw [← Subgroup.relIndex_ker (M.subgroupOf SE) D.φ, D.ker,
      Subgroup.relIndex_subgroupOf (H := Work.GW2.zE B) hMSE]
  rw [show Work.GW2.kE B = Z.relIndex M from rfl, ← hcard, hmap]

end Work.CORE2A
