import Submission.Work.Engulf.Tools
import Submission.Work.PL.Generic.GpPairs
import Submission.Work.Geo.Prism.Push
import Submission.Work.Geo.Prism.PushRel.prism_push_rel
import Submission.Work.Geo.Radial.ext_homeo_open
import Submission.Work.PL.Subdiv.Simplex.exists_homeomorph_simp_closedBall
import Submission.Work.Engulf.Auxi.Carrier
import Submission.Work.PL.Subdiv.Util.union_of_faces_sdIter
import Submission.Work.PL.Subdiv.Util.Mesh.exists_fine_general
import Submission.Work.Engulf.Auxi.vertexPerturbForm
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_faces

/-!
# Discharging the fields of `Work.Engulf.Tools` with the real results of the other areas

Each lemma below is the exact instance of a `Tools` field that the area owning it has already
delivered and proved (axiom-clean).  They are stated as separate lemmas so that a
caller can build the corresponding `Tools` field; as the remaining areas deliver
(`PL.Approx`'s frozen `pl_approx`, `PL.Subdiv`'s shelling/mesh/carrier, `Geo.Prism`'s
`join_simplex_prism`, the vertex perturbation), the missing fields can be added here in the same
shape, and then `ToolsAll n` becomes an unconditional term.

* `gp_form`           — A3, `Work.PL.Generic.gp_pairs`;
* `prismPush_form`    — A1, `Work.Geo.Prism.prism_push`;
* `prismPushRel_form` — A1, `Work.Geo.Prism.PushRel.prism_push_rel`;
* `simplexBall_form`  — A2, `Work.PL.Subdiv.Simplex.exists_homeomorph_simp_closedBall`;
* `extHomeo_form`     — A7, `Work.Geo.Radial.ext_homeo_open`;
* `carrier_form`      — A2, `Work.Engulf.exists_coarse_face_of_simp_subset`;
* `sdIter_subsp`      — A2, `SubdivTools.subsp` for the concrete `Work.PL.Subdiv.sdIter`;
* `sdIter_fine`       — A2, `SubdivTools.fine` for the concrete `Work.PL.Subdiv.sdIter`;
* `vertexPerturb_form` — A5/A9, `Work.Engulf.Auxi.vertexPerturbForm`.
-/

open Set Metric PL

namespace Work.Engulf

universe u

/-- A3: the corrected general position form `G6a'` of contract §4.1, from
`Work.PL.Generic.gp_pairs`. -/
theorem gp_form (n : ℕ) : GPaForm.{u} n :=
  fun fz y₀ Pairs Fixed hfree hcard hnd₁ hnd₂ hcol ε hε =>
    Work.PL.Generic.gp_pairs fz y₀ Pairs Fixed hfree hcard hnd₁ hnd₂ hcol ε hε

/-- A1: the prism push `G1`, from `Work.Geo.Prism.prism_push`. -/
theorem prismPush_form : PrismPushForm :=
  fun F hF φ γ hφ hγ hle hfr U W hU hW hbase hS =>
    Work.Geo.Prism.prism_push F hF φ γ hφ hγ hle hfr U W hU hW hbase hS

/-- A1: the relative prism push `G1'` (Newman Theorem 2), from
`Work.Geo.Prism.PushRel.prism_push_rel`. -/
theorem prismPushRel_form : PrismPushRelForm :=
  fun F J hF hJ hJF γ₀ γ₁ h₀ h₁ hle hfr U W A hU hW hA hAU hbase hJU hS hAS =>
    Work.Geo.Prism.PushRel.prism_push_rel F J hF hJ hJF γ₀ γ₁ h₀ h₁ hle hfr U W A hU hW
      hA hAU hbase hJU hS hAS

/-- A2 item 8: a simplex is a ball, from
`Work.PL.Subdiv.Simplex.exists_homeomorph_simp_closedBall`. -/
theorem simplexBall_form : SimplexBallForm :=
  fun s hs hind => Work.PL.Subdiv.Simplex.exists_homeomorph_simp_closedBall s hs hind

/-- A7 (`C0`): extending a homeomorphism of an open subspace, from
`Work.Geo.Radial.ext_homeo_open`. -/
theorem extHomeo_form : ExtHomeoOpenForm.{u} :=
  fun O hO h C hC hid => Work.Geo.Radial.ext_homeo_open O hO h C hC hid

/-- A2: the carrier property of the subdivision (the extra field of `Tools`), from
`Work.Engulf.exists_coarse_face_of_simp_subset`. -/
theorem carrier_form {N : ℕ} (S : SubdivTools N) :
    ∀ r (K : Cx N) (hK : K.faces.Finite) (L : Set (E N)), IsSubSp K L →
      ∀ s' ∈ (S.sdIter r K hK).faces, simp s' ⊆ L →
        ∃ s ∈ K.faces, simp s' ⊆ simp s ∧ simp s ⊆ L :=
  fun r K hK L hLK s' hs' hs'L =>
    let ⟨τ, hτ, hτL, hs'τ⟩ :=
      Work.Engulf.exists_coarse_face_of_simp_subset S hLK hs' hs'L
    ⟨τ, hτ, hs'τ, hτL⟩

/-- A2: `SubdivTools.subsp` for the concrete barycentric subdivision
`Work.PL.Subdiv.sdIter`, from `Work.PL.Subdiv.Util.union_of_faces_sdIter`. -/
theorem sdIter_subsp {N : ℕ} (r : ℕ) (K : Cx N) (hK : K.faces.Finite) (S : Set (E N))
    (hS : IsSubSp K S) : IsSubSp (Work.PL.Subdiv.sdIter r K hK) S := by
  obtain ⟨T', hT', hEq⟩ := Work.PL.Subdiv.Util.union_of_faces_sdIter hS.1 hS.2 r hK
  rw [hEq]
  exact isSubSp_of_faces hT'

/-- A2: `SubdivTools.fine` for the concrete barycentric subdivision, from
`Work.PL.Subdiv.Util.Mesh.exists_fine_general`. -/
theorem sdIter_fine {N : ℕ} (K : Cx N) (hK : K.faces.Finite) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r, ∀ r' ≥ r, MeshLT (Work.PL.Subdiv.sdIter r' K hK) δ :=
  Work.PL.Subdiv.Util.Mesh.exists_fine_general K hK δ hδ

/-- A5/A9: the vertex perturbation realising `G6a'`, from
`Work.Engulf.Aux.vertexPerturbForm`. -/
theorem vertexPerturb_form (N n : ℕ) : VertexPerturbForm N n :=
  Work.Engulf.Aux.vertexPerturbForm N n

/-- A5: the frozen PL approximation *at a given level* of the subdivision (E4 repair), from A5's
proved `Work.PL.Approx.Frozen.pl_approx_frozen_faces`. -/
theorem plApproxAt_form {N : ℕ} (S : SubdivTools N) (n : ℕ) : PlApproxFrozenAtForm S n := by
  classical
  intro K hK r L hL f hf α β hα hαβ hβ ε hε hlin hosc
  have hfin := S.fin r K hK
  set T : Finset (Finset (E N)) := hfin.toFinset.filter (fun s => simp s ⊆ L) with hT
  obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ :=
    Work.PL.Approx.Frozen.pl_approx_frozen_faces K (S.sdIter r K hK) hfin f hf (S.subdiv r K hK)
      α β hα hαβ hβ ε hε T
      (fun t ht => (hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1))
      (fun t ht hz => by
        obtain ⟨A, hA⟩ := hlin t (hfin.mem_toFinset.1 (Finset.mem_filter.1 ht).1)
          (Finset.mem_filter.1 ht).2 hz
        exact ⟨A, fun z hz => hA hz⟩)
      hosc
  refine ⟨g, hg1, hg2, ?_, hg3, fun s hs hx => ?_⟩
  · intro x hx
    obtain ⟨t, ht, hxt, htL⟩ := hL.2 x hx
    exact hg4 t (Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ht, htL⟩) x hxt
  · obtain ⟨A, hA⟩ := hg5 s hs hx
    exact ⟨A, fun y hy => hA y hy⟩

/-! ## Assembling `Tools` and `ToolsAll` from the delivered results

`subdivTools` builds `SubdivTools N` on the concrete barycentric subdivision
`Work.PL.Subdiv.sdIter`; the only field not yet delivered by A2 is the shelling `G4` of A4, so it
is taken as an explicit hypothesis (of the same shape as the field).  `tools` then assembles a
full `Tools N n` out of that and the three remaining forms (`plApprox`, `vertexPerturb`,
`joinPrism`), and `toolsAll` the uniform family.  Discharging the three remaining names with the
real results of A5 and A1 makes `Work.Engulf.engulf` unconditional. -/

/-- The shelling data of `SubdivTools` for the concrete barycentric subdivision: the type of the
`shell` field, written at `sdIter := Work.PL.Subdiv.sdIter`. -/
abbrev SubdivShellForm (N : ℕ) : Prop :=
  ∀ r (K : Cx N) (hK : K.faces.Finite) (Δ τ₁ : Finset (E N)), Δ ∈ K.faces → τ₁.Nonempty →
    τ₁ ⊂ Δ →
    ∃ ord : List (Finset (E N)), ord.Nodup ∧
      (∀ τ ∈ ord, τ ∈ (Work.PL.Subdiv.sdIter r K hK).faces ∧
        τ.card = Δ.card ∧ simp τ ⊆ simp Δ) ∧
      (⋃ τ ∈ ord, simp τ) = simp Δ ∧
      ∀ i (hi : i < ord.length), ∃ τ₁' : Finset (E N), τ₁'.Nonempty ∧ τ₁' ⊂ ord[i] ∧
        simp ord[i] ∩ ((⋃ w ∈ τ₁, simp (Δ.erase w)) ∪
          ⋃ j ∈ Finset.range i, ⋃ (hj : j < ord.length), simp ord[j]) =
          ⋃ w ∈ τ₁', simp (ord[i].erase w)

/-- `SubdivTools N` on the concrete barycentric subdivision of A2, from the shelling of A4. -/
noncomputable def subdivTools {N : ℕ} (shell : SubdivShellForm N) : SubdivTools N :=
  SubdivTools.mk Work.PL.Subdiv.sdIter
    (fun r K hK => Work.PL.Subdiv.sdIter_faces_finite r K hK)
    (fun K hK => Work.PL.Subdiv.sdIter_zero K hK)
    (fun r K hK => Work.PL.Subdiv.sdIter_subdivides r K hK)
    (fun r K hK S hS => sdIter_subsp r K hK S hS)
    (fun r K hK d h => Work.PL.Subdiv.sdIter_dimle r d K hK h)
    (fun K hK δ hδ => sdIter_fine K hK δ hδ)
    shell

/-- A full `Tools N n`, given the three forms of A5/A1 that are not yet delivered by name. -/
noncomputable def tools {N n : ℕ} (shell : SubdivShellForm N)
    (plApprox : PlApproxFrozenForm (subdivTools shell) n)
    (full : SdFullForm (subdivTools shell))
    (joinPrism : JoinPrismForm N) : Tools N n where
  subdiv := subdivTools shell
  carrier := carrier_form (subdivTools shell)
  plApprox := plApprox
  plApproxAt := plApproxAt_form (subdivTools shell) n
  full := full
  vertexPerturb := vertexPerturb_form N n
  prismPush := prismPush_form
  prismPushRel := prismPushRel_form
  joinPrism := joinPrism
  simplexBall := simplexBall_form
  gp := gp_form n
  extHomeo := extHomeo_form

/-- The uniform family `ToolsAll n`, given the remaining forms for every ambient dimension. -/
noncomputable def toolsAll {n : ℕ} (shell : ∀ N, SubdivShellForm N)
    (plApprox : ∀ N, PlApproxFrozenForm (subdivTools (shell N)) n)
    (full : ∀ N, SdFullForm (subdivTools (shell N)))
    (joinPrism : ∀ N, JoinPrismForm N) : ToolsAll.{u} n :=
  fun N => tools (shell N) (plApprox N) (full N) (joinPrism N)

end Work.Engulf
