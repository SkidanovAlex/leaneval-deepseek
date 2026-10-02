/-
# SeedDyn — the dynamical Böttcher homeomorphism for `c ∈ M*` (D12)

This module assembles the D-table of `Submission/Work/NOTES_LEAD_mandelbar_seed.md` §1.3 into
the area's headline result:

* `Work.SeedDyn.dynBottcherHomeo (hc : c ∈ Mandelbar) : Work.ParamRays.DynBottcherHomeo c` —
  the dynamical Böttcher coordinate of `T_c` is a homeomorphism of the escaping set onto the
  exterior disc;
* `Work.SeedDyn.isDynBottcherHomeo` — the same, in `Work.Landing`'s interface
  `IsDynBottcherHomeo c (dynPhiOf c)` (injectivity on the escaping set + surjectivity onto the
  exterior disc, on top of `IsDynBottcher`);
* `Work.SeedDyn.dynB (hc) : Work.ELPull.DynB c` — the dynamical Nakane data, for the `EL`/`FSeed`
  consumers (`Work.ParamRays.dynNakane (dynBottcherHomeo hc)`);
* `Work.SeedDyn.dynBottcherExists_of_dynB` — conversely, `Work.ELPull.DynB c` is only inhabited
  when a Böttcher coordinate exists (non-vacuity).

The chain is the one designed in the note: `varphiCrit c` is analytic on `esc c` with nonvanishing
derivative (D3, D4, D5, D6, D7), hence a local homeomorphism (D8); it is injective far out (D9) and
proper into the exterior disc (D10); `G_c` controls its growth (D11, `hbdd`); the generic lemma
`homeo_of_proper_localHomeo` concludes.  On the escaping set `varphiCrit c` coincides with the
canonical dynamical Böttcher coordinate `dynPhiOf c` (D2).
-/
import Mathlib
import Submission.Work.SeedDyn.Defs
import Submission.Work.SeedDyn.homeo_of_proper_localHomeo
import Submission.Work.SeedDyn.varphiCrit_comm_Tsq
import Submission.Work.SeedDyn.deriv_Tsq_ne_zero
import Submission.Work.SeedDyn.deriv_varphiCrit_tendsto_one
import Submission.Work.SeedDyn.deriv_varphiCrit_ne_zero
import Submission.Work.SeedDyn.isLocalHomeomorphOn_varphiCrit
import Submission.Work.SeedDyn.injOn_varphiCrit_far
import Submission.Work.SeedDyn.isCompact_varphiCrit_preimage
import Submission.Work.SeedDyn.bdd_varphiCrit_on_ball
import Submission.Work.SeedDyn.grow_varphiCrit
import Submission.Work.ParamRays.DynNakane
import Submission.Work.Bottcher.CritBottcherExists
import Submission.Work.Landing.Rays
import Submission.Work.ELPull.pb1
import Submission.Work.Top.mem_paramRay_extAngle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Classical Filter

namespace Work.SeedDyn

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Transport of subtypes along an equality of sets -/

/-- The canonical homeomorphism `↥s ≃ₜ ↥t` induced by an equality of carrier sets. -/
def homeoOfSetEq {s t : Set ℂ} (h : s = t) : ↥s ≃ₜ ↥t where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

@[simp] theorem homeoOfSetEq_apply {s t : Set ℂ} (h : s = t) (x : ↥s) :
    ((homeoOfSetEq h x : ↥t) : ℂ) = (x : ℂ) := rfl

/-! ## D7 and the local homeomorphism (D8) -/

/-- **D7.**  The derivative of the critical Böttcher coordinate does not vanish on the escaping
set. -/
theorem deriv_varphiCrit_ne_zero_esc {c : ℂ} (hc : c ∈ Mandelbar) {z : ℂ} (hz : z ∈ esc c) :
    deriv (Work.Bottcher.varphiCrit c) z ≠ 0 :=
  deriv_varphiCrit_ne_zero hc
    (fun w hw => varphiCrit_comm_Tsq hc hw)
    (fun w hw => deriv_Tsq_ne_zero hc hw)
    (deriv_varphiCrit_tendsto_one hc) hz

/-! ## The D-table with the inputs discharged

The modules `deriv_varphiCrit_ne_zero`, `isLocalHomeomorphOn_varphiCrit` and `injOn_varphiCrit_far`
state D7, D8 and D9 with their inputs (D4–D6, D7, D6 respectively) as hypotheses, so that they can
be proved independently of one another.  Here the inputs are discharged, giving the statements of
the design note's §1.3 table verbatim. -/

/-- **D7**, closed form: `deriv (varphiCrit c)` has no zeros on the escaping set. -/
theorem deriv_varphiCrit_ne_zero' {c : ℂ} (hc : c ∈ Mandelbar) {z : ℂ} (hz : z ∈ esc c) :
    deriv (Work.Bottcher.varphiCrit c) z ≠ 0 :=
  deriv_varphiCrit_ne_zero_esc hc hz

/-- **D8**, closed form: for `c ∈ M*` the critical Böttcher coordinate is a local
homeomorphism on the escaping set. -/
theorem isLocalHomeomorphOn_varphiCrit' {c : ℂ} (hc : c ∈ Mandelbar) :
    IsLocalHomeomorphOn (Work.Bottcher.varphiCrit c) (esc c) :=
  isLocalHomeomorphOn_varphiCrit hc (fun z hz => deriv_varphiCrit_ne_zero_esc hc hz)

/-- **D9**, closed form: `varphiCrit c` is injective on a far annulus. -/
theorem injOn_varphiCrit_far' {c : ℂ} (hc : c ∈ Mandelbar) :
    ∃ R : ℝ, {z : ℂ | R ≤ ‖z‖} ⊆ esc c ∧
      Set.InjOn (Work.Bottcher.varphiCrit c) {z : ℂ | R ≤ ‖z‖} :=
  injOn_varphiCrit_far hc (deriv_varphiCrit_tendsto_one hc)

/-! ## D12: the homeomorphism on the escaping set -/

/-- **D12 (assembly).**  For `c ∈ M*` the critical Böttcher coordinate `varphiCrit c` maps the
escaping set `esc c` homeomorphically onto the exterior disc.

The generic lemma `homeo_of_proper_localHomeo` is applied with `U := esc c` and `f := varphiCrit c`:
the five hypotheses are D8 (locality), D10 (properness), `bdd_varphiCrit_on_ball`, D9 (far
injectivity) and D11 (coercivity). -/
theorem exists_homeo_esc {c : ℂ} (hc : c ∈ Mandelbar) :
    ∃ e : ↥(esc c) ≃ₜ ↥Work.Top.exteriorDisc,
      ∀ z : ↥(esc c), Work.Bottcher.varphiCrit c z = (e z : ℂ) :=
  homeo_of_proper_localHomeo (isOpen_esc c)
    (fun z hz => one_lt_norm_varphiCrit_esc hc hz)
    (isLocalHomeomorphOn_varphiCrit hc (fun z hz => deriv_varphiCrit_ne_zero_esc hc hz))
    (fun K hK hK1 => isCompact_varphiCrit_preimage hc hK hK1)
    (bdd_varphiCrit_on_ball hc)
    (injOn_varphiCrit_far hc (deriv_varphiCrit_tendsto_one hc))
    (grow_varphiCrit hc)

/-- **The dynamical Böttcher homeomorphism for `c ∈ M*`.**

This is the seed's `dyn` input (`Work.FSeed.RootParabolicInput.dyn`), the first half of
`Work.LANDCL.HyperbolicContraction`, and the surjectivity producer for `Landing`'s
`IsDynBottcherHomeo`. -/
theorem dynBottcherHomeo {c : ℂ} (hc : c ∈ Mandelbar) :
    Work.ParamRays.DynBottcherHomeo c := by
  obtain ⟨e, he⟩ := exists_homeo_esc hc
  refine ⟨Work.Bottcher.exists_isDynBottcher_of_mem_mandelbar c hc, ?_⟩
  let e' : ↥((Work.ParamRays.filledJulia c)ᶜ) ≃ₜ ↥Work.Top.exteriorDisc :=
    (homeoOfSetEq (esc_eq_compl_filledJulia c)).symm.trans e
  refine ⟨e', ?_⟩
  intro z
  have hzF : (z : ℂ) ∉ Work.ParamRays.filledJulia c := z.2
  have hzesc : (z : ℂ) ∈ esc c := by rw [esc_eq_compl_filledJulia]; exact hzF
  have h3 : (e' z : ℂ) = (e ⟨(z : ℂ), hzesc⟩ : ℂ) := rfl
  rw [h3, ← he ⟨(z : ℂ), hzesc⟩, ← dynPhiOf_eq_varphiCrit hc hzesc]
  exact Work.ParamRays.dynPhi_of_not_mem hzF

/-- **The dynamical Böttcher homeomorphism, in `Work.Landing`'s interface.**

`Work.Landing.IsDynBottcherHomeo c φ` is `IsDynBottcher c φ` together with injectivity on the
escaping set and surjectivity onto the exterior disc.  It is exactly what the ray-transfer
lemmas (`rayAccum_image_homeo`, `Caratheodory`) consume. -/
theorem isDynBottcherHomeo {c : ℂ} (hc : c ∈ Mandelbar) :
    Work.Landing.IsDynBottcherHomeo c (Work.ParamRays.dynPhiOf c) := by
  obtain ⟨hex, e, he⟩ := dynBottcherHomeo hc
  -- the Böttcher coordinate is the homeomorphism on the complement of the filled Julia set
  have key : ∀ (z : ℂ) (hz : z ∉ Work.ParamRays.filledJulia c),
      Work.Bottcher.varphiCrit c z = (e ⟨z, hz⟩ : ℂ) := by
    intro z hz
    have hzesc : z ∈ esc c := by rw [esc_eq_compl_filledJulia]; exact hz
    rw [← dynPhiOf_eq_varphiCrit hc hzesc, ← Work.ParamRays.dynPhi_of_not_mem hz]
    exact he ⟨z, hz⟩
  refine ⟨Work.ParamRays.isDynBottcher_dynPhiOf hex, ?_, ?_⟩
  · intro z w hz hw h
    have hzesc : z ∈ esc c := hz
    have hwesc : w ∈ esc c := hw
    have hzF : z ∉ Work.ParamRays.filledJulia c := by
      rw [esc_eq_compl_filledJulia] at hzesc; exact hzesc
    have hwF : w ∉ Work.ParamRays.filledJulia c := by
      rw [esc_eq_compl_filledJulia] at hwesc; exact hwesc
    have h' : Work.Bottcher.varphiCrit c z = Work.Bottcher.varphiCrit c w := by
      rw [← dynPhiOf_eq_varphiCrit hc hz, ← dynPhiOf_eq_varphiCrit hc hw]
      exact h
    have h'' : (e ⟨z, hzF⟩ : ℂ) = (e ⟨w, hwF⟩ : ℂ) := by
      rw [← key z hzF, ← key w hwF]
      exact h'
    exact Subtype.ext_iff.mp (e.injective (Subtype.ext h''))
  · intro w hw
    let x : ↥((Work.ParamRays.filledJulia c)ᶜ) := e.symm ⟨w, hw⟩
    refine ⟨(x : ℂ), ?_, ?_⟩
    · exact (Work.ParamRays.escaping_iff_not_bounded c (x : ℂ)).mpr x.2
    · have h1 : Work.Bottcher.varphiCrit c (x : ℂ) = w := by
        rw [key (x : ℂ) x.2]
        exact congrArg Subtype.val (Homeomorph.apply_symm_apply e ⟨w, hw⟩)
      rw [dynPhiOf_eq_varphiCrit hc (by rw [esc_eq_compl_filledJulia]; exact x.2), h1]

/-- **The dynamical Nakane data at `c ∈ M*`** (the `hN` of the `EL`/`FSeed` areas): the
dynamical Böttcher homeomorphism `esc c ≃ₜ exteriorDisc` together with the potential and its
coercivity, packaged as `Work.Top.NakaneData (filledJulia c) (dynPhi c)`. -/
noncomputable def dynB {c : ℂ} (hc : c ∈ Mandelbar) : Work.ELPull.DynB c :=
  Work.ParamRays.dynNakane (dynBottcherHomeo hc)

/-! ## Every escaping point lies on a ray -/

/-- **Every point of the escaping set lies on a dynamical external ray.**  This is the
surjectivity half of the dynamical Böttcher homeomorphism, in the ray vocabulary: the ledger's
`hcover` (`∀ z ∉ K c, ∃ ϑ, z ∈ paramRay hN ϑ`). -/
theorem exists_paramRay_of_notMem {c : ℂ} (hN : Work.ELPull.DynB c) {z : ℂ}
    (hz : z ∉ Work.ParamRays.filledJulia c) : ∃ ϑ : ℝ, z ∈ hN.paramRay ϑ :=
  ⟨Work.Top.NakaneData.extAngle (Work.ParamRays.dynPhi c) z,
    Work.Top.mem_paramRay_extAngle hN hz⟩

/-! ## Non-vacuity of the dynamical Nakane data -/

/-- **`Work.ELPull.DynB c` is inhabited only when a Böttcher coordinate exists.**  If
`DynBottcherExists c` failed then `dynPhi c` would be the junk value `≡ 0`, contradicting
`hN.he` (which forces `1 < ‖dynPhi c z‖` for `z` off the filled Julia set, and `filledJulia c ≠ ℂ`
because far-away points escape). -/
theorem dynBottcherExists_of_dynB {c : ℂ} (hN : Work.ELPull.DynB c) :
    Work.ParamRays.DynBottcherExists c :=
  Work.ELPull.dynBottcherExists_of_dynB hN

/-- **The converse**: every `Work.ELPull.DynB c` *is* a dynamical Böttcher homeomorphism, with
the same homeomorphism and the same identification `dynPhi c z = e z`.  Together with
`Work.SeedDyn.dynB` this identifies the two interfaces (`Work.ELPull.DynB c` is inhabited exactly
for `c ∈ M*`). -/
theorem dynBottcherHomeo_of_dynB {c : ℂ} (hN : Work.ELPull.DynB c) :
    Work.ParamRays.DynBottcherHomeo c :=
  ⟨dynBottcherExists_of_dynB hN, hN.e, hN.he⟩

/-- The dynamical Böttcher coordinate attached to any `Work.ELPull.DynB c` is an honest
Böttcher coordinate.  This is the `hφ` input of the ray-transfer lemmas
(`Work.ELPull.rayPt_Tantibar`, `landsN_image`). -/
theorem isDynBottcher_dynPhiOf_of_dynB {c : ℂ} (hN : Work.ELPull.DynB c) :
    Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
  Work.ParamRays.isDynBottcher_dynPhiOf (dynBottcherExists_of_dynB hN)

end

end Work.SeedDyn
