import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.TransferReduction
import Submission.Work.SSGRoute.ZConstruction.exists_junkSpan_complement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `z`-data from the *per-datum* no-gap gate, and the exact residual case

`Work.SSGRoute.ZConstruction.ZDataAux` proves the §4 induction step against the **uniform**
auxiliary-class obligation `Work.SSGRoute.AuxExists` together with the **uniform** no-gap provision
`Work.SSGRoute.ZConstruction.AuxGapProv` (through
`Work.SSGRoute.ZConstruction.z_data_general_of_unmixed_gates_gap`).  Neither uniform statement is
implied by the node's hypotheses:

* the no-gap provision `AuxGapProv` asks the no-gap condition `AuxGapFun K Λ S N ν` for *every*
  one-dimensional `ZHyp` datum `ν`, while a datum may well be ramified at a `Λ`-split place outside
  `cs(S)` that is not `N`-split;
* consequently the *correct* obligation is the per-datum one
  `Work.SSGRoute.ZConstruction.AuxExistsGap` (the same statement with `AuxGapFun K Λ S N y₁` as an
  extra hypothesis on the datum *at hand*), which *is* derivable from the pairing gate and the
  unmixed realisation gate alone
  (`Work.SSGRoute.ZConstruction.auxExistsGap_of_pairing_and_unmixed`, proved).

This file performs the matching repair of the induction step, and isolates the exact residual case.

* **`z_data_of_spanning_of_auxGap`** -- the spanning step of §4 against `AuxExistsGap`, using the
  line decomposition `E = E₀ ⊕ L` with `E₀ ⊇ junkSpan K Λ S y` supplied by
  `Work.SSGRoute.ZConstruction.exists_junkSpan_complement`: the projection `π₁` onto `L` kills the
  whole junk span, hence `π₁ ∘ y` satisfies `AuxGapFun` at *every* level
  (`auxGapFun_comp_of_junkSpan_le`), which is exactly the extra hypothesis of `AuxExistsGap`.
  This step therefore needs one extra hypothesis on the datum, namely that its junk ramification is
  *proper*: `junkSpan K Λ S y ≠ ⊤`.

* **`z_data_general_of_auxGap_and_caseC`** -- the strong induction on `dim_{𝔽_p} E`, with the gate
  list `MupGate` + `AuxExistsGap` + the **Case C gate**

      ∀ y, ZHyp y → csData K S y = ⊤ → junkSpan K Λ S y = ⊤ → ∃ z, HasZData K Λ S y z.

  The three cases of the induction are

  1. `dim E ≤ 1`: `MupGate`;
  2. `csData K S y ≠ ⊤`: the *peeling* step -- project onto the span of the `cs(S)`-local data and
     apply the induction hypothesis to the projected datum (the projection fixes `y` on the local
     groups, so `hasZData_of_fixes_data` transfers the witness back);
  3. `csData K S y = ⊤`: either `junkSpan K Λ S y ≠ ⊤`, which is the spanning step against
     `AuxExistsGap` above, or `junkSpan K Λ S y = ⊤`, which is **Case C**, the gate carried as a
     hypothesis.

  Case C is the exact residual: the datum's prescribed local data *and* its junk ramification both
  span the coefficient module, so there is no line `L` with `E₀ = ker π₁ ⊇ junkSpan K Λ S y`, and the
  product-formula chase (which produces the orthogonality against the dual family only for a datum
  unramified at the `Λ`-split `¬N`-split places) does not apply.  This is the case in which the
  paper's p. 18 argument is not a product formula but the decomposition `ν = (ν₁, ν₂)` along `K ≤ K̃`
  (unramified at the places of `T(K)`).  In Case C the datum is *pinned* on all of `E`
  (`csData = ⊤`), so no projection of the datum can remove the junk ramification: every additive
  `π : E → E` fixing the `cs(S)`-local values of `y` is the identity.

The residue `junkSpan K Λ S y ≠ ⊤` in the spanning step is *not* an artefact of the strong
induction: the induction hypothesis is the *full* statement at all smaller dimensions, so the
step is used only once per dimension, and the projected datum `π₀ ∘ y` (whose junk span equals
`junkSpan K Λ S y`, since `π₀` is the identity on `E₀ ⊇ junkSpan`) is handled by the hypothesis.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-- **The spanning step of §4 against the per-datum no-gap gate.**

Given the induction hypothesis at all smaller coefficient modules, the one-dimensional gate, the
*per-datum* auxiliary-class obligation `AuxExistsGap`, and a datum whose junk ramification is
proper (`junkSpan K Λ S y ≠ ⊤`), the `z`-data holds for a datum whose `cs(S)`-local data spans the
coefficient module of dimension `≥ 2`. -/
theorem z_data_of_spanning_of_auxGap {K Λ : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    (hAmb : ZAmbient (p := p) K Λ S) (hmup : MupGate (p := p) K)
    (haux : ZConstruction.AuxExistsGap (p := p) K Λ S)
    (hIH : ∀ (E' : Type) [AddCommGroup E'] [Module (ZMod p) E'] [Finite E'],
      Module.finrank (ZMod p) E' < Module.finrank (ZMod p) E →
      ∀ y' : (Ω ≃ₐ[k] Ω) → E', ZHyp (p := p) K Λ S y' →
      ∃ z' : (Ω ≃ₐ[k] Ω) → E', HasZData K Λ S y' z')
    (y : (Ω ≃ₐ[k] Ω) → E) (hy : ZHyp (p := p) K Λ S y)
    (hspan : csData (p := p) K S y = ⊤)
    (hdim : 2 ≤ Module.finrank (ZMod p) E)
    (hproper : ZConstruction.junkSpan K Λ S y ≠ ⊤) :
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  classical
  -- 1. the splitting `E = L ⊕ E₀` with `E₀ ⊇ junkSpan`, and the line component `y₁`
  obtain ⟨Lsub, E₀, _hc, hL1, hE₀lt, hsub, π₀, π₁, hsum, hπ₀, _hπ₁, _hkill⟩ :=
    ZConstruction.exists_junkSpan_complement (p := p) (K := K) (Λ := Λ) (S := S) y hdim hproper
  set y₀ : (Ω ≃ₐ[k] Ω) → ↥E₀ := fun σ => π₀ (y σ) with hy₀
  set y₁ : (Ω ≃ₐ[k] Ω) → ↥Lsub := fun σ => π₁ (y σ) with hy₁
  have hy₀hyp : ZHyp (p := p) K Λ S y₀ := ZHyp.mapAdd (f := π₀.toAddMonoidHom) hy
  have hy₁hyp : ZHyp (p := p) K Λ S y₁ := ZHyp.mapAdd (f := π₁.toAddMonoidHom) hy
  -- the projection `π₁` kills `E₀`, so `π₁ ∘ y` satisfies the no-gap condition at every level
  have hkillE₀ : ∀ x ∈ E₀.toAddSubgroup, π₁ x = 0 := by
    intro x hx
    have hx' : (π₀ x : E) = x := hπ₀ x hx
    have h2 : x + (π₁ x : E) = x := by
      have h3 : (π₀ x : E) + (π₁ x : E) = x := hsum x
      rwa [hx'] at h3
    have h1 : (π₁ x : E) = 0 := by
      have h3 : x + (π₁ x : E) = x + 0 := by rw [add_zero, h2]
      exact add_left_cancel h3
    exact Subtype.ext h1
  -- 2. the induction hypothesis at the hyperplane `E₀`
  obtain ⟨z₀', hz₀'⟩ := hIH ↥E₀ hE₀lt y₀ hy₀hyp
  -- 3. transport `z₀'` to `E` and take its level
  have hz₀E : HasZData K Λ S (fun σ => (π₀ (y σ) : E)) (fun σ => (z₀' σ : E)) :=
    hasZData_map (A := ↥E₀) (B := E) (f := (Submodule.subtype E₀).toAddMonoidHom)
      (fun _ _ h => Subtype.ext h) hz₀'
  set z₀ : (Ω ≃ₐ[k] Ω) → E := fun σ => (z₀' σ : E) with hz₀
  obtain ⟨N₀, hKN₀, hN₀fin, hN₀gal, hN₀v⟩ :=
    exists_level_vanishing_finite (K := K) hz₀E.1 hz₀E.2.1
  haveI : FiniteDimensional k N₀ := hN₀fin
  haveI : IsGalois k N₀ := hN₀gal
  haveI : FiniteDimensional k ↥(N₀ ⊔ Λ) := IntermediateField.finiteDimensional_sup N₀ Λ
  haveI : IsGalois k ↥(N₀ ⊔ Λ) := inferInstance
  have hΛN : Λ ≤ N₀ ⊔ Λ := le_sup_right
  have hNv : ∀ g ∈ (N₀ ⊔ Λ).fixingSubgroup, z₀ g = 0 :=
    fun g hg => hN₀v g (IntermediateField.fixingSubgroup_le le_sup_left hg)
  -- 4. the enlarged place set
  obtain ⟨S', hS'fin, hS'disj, hS'sub, hS'ram⟩ :=
    ZConstruction.exists_finset_ramifiedPlaces p (Fact.out : p.Prime) k Ω (N₀ ⊔ Λ) S
      hAmb.hSfin hAmb.hSdisj
  -- 5. the auxiliary class at `(N,S')`, with the per-datum no-gap hypothesis
  have hgapfun : ZConstruction.AuxGapFun K Λ S (N₀ ⊔ Λ) y₁ :=
    ZConstruction.auxGapFun_comp_of_junkSpan_le (K := K) (Λ := Λ) (N := N₀ ⊔ Λ) (S := S)
      y E₀.toAddSubgroup hsub π₁.toAddMonoidHom hkillE₀
  obtain ⟨yAux, hyAuxHyp, hyAuxAgree, hyAuxVanish⟩ :=
    haux (N₀ ⊔ Λ) hΛN S' hS'fin hS'disj hS'sub (fun B hB hram => hS'ram B hB (Or.inl hram))
      ↥Lsub hL1 y₁ hy₁hyp hgapfun
  have hAmbN : ZAmbient (p := p) K (N₀ ⊔ Λ) S' :=
    { hKΛ := le_trans hAmb.hKΛ hΛN, ζ := hAmb.ζ, hζ := hAmb.hζ, hζK := hAmb.hζK,
      hSfin := hS'fin, hSdisj := hS'disj,
      hSram := fun B hB hram => hS'ram B hB hram }
  obtain ⟨z₁', hz₁'⟩ := hmup (N₀ ⊔ Λ) S' hAmbN ↥Lsub hL1.le yAux hyAuxHyp
  have hz₁E : HasZData K (N₀ ⊔ Λ) S' (fun σ => (yAux σ : E)) (fun σ => (z₁' σ : E)) :=
    hasZData_map (A := ↥Lsub) (B := E) (f := (Submodule.subtype Lsub).toAddMonoidHom)
      (fun _ _ h => Subtype.ext h) hz₁'
  -- 6. the level `N` is normal, and the assembly
  have hNnorm : ((N₀ ⊔ Λ).fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)).Normal :=
    IsGalois.fixingSubgroup_normal_of_isGalois (N₀ ⊔ Λ)
  have hmain : HasZData K Λ S (fun σ => (π₀ (y σ) : E) + (π₁ (y σ) : E))
      (z₀ + fun σ => (z₁' σ : E)) :=
    hasZData_sum_of_level_data (K := K) (Λ := Λ) (N := N₀ ⊔ Λ) (S := S) (S' := S')
      (y := fun σ => (π₀ (y σ) : E) + (π₁ (y σ) : E))
      (y₀ := fun σ => (π₀ (y σ) : E)) (y₁ := fun σ => (π₁ (y σ) : E))
      (yAux := fun σ => (yAux σ : E)) (z₀ := z₀) (z₁ := fun σ => (z₁' σ : E))
      hNnorm hΛN
      (fun B hB => hS'sub B hB)
      (fun B hB hram => hS'ram B hB (Or.inl hram))
      (fun σ => rfl)
      hz₀E
      (fun g hg => hNv g hg)
      hz₁E
      (fun B hB hconj σ hσ => congrArg Subtype.val (hyAuxAgree B hB hconj σ hσ))
      (fun B hB hnot hS' σ hσ => congrArg Subtype.val (hyAuxVanish B hB hnot hS' σ hσ))
  exact ⟨z₀ + fun σ => (z₁' σ : E),
    hasZData_congr (fun σ => hsum (y σ)) hmain⟩

/-- **The Case C gate**: the `z`-data for the data whose prescribed (`cs(S)`-local) data *and* whose
junk ramification both span the coefficient module.

This is the exact residual of the gate-based route: in Case C neither the peeling step (which needs
`csData ≠ ⊤`) nor the spanning step with a line complement of the junk span (which needs
`junkSpan ≠ ⊤`) applies, and the datum is pinned on all of `E` by its `cs(S)`-local values, so no
projection of the datum can remove the junk ramification. -/
def CaseCGate (p : ℕ) [Fact p.Prime] (K : IntermediateField k Ω) : Prop :=
  ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
    (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
    ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
    ZHyp (p := p) K Λ S y → csData (p := p) K S y = ⊤ →
    ZConstruction.junkSpan K Λ S y = ⊤ →
    ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z

/-- **The `z`-data from the one-dimensional gate, the per-datum auxiliary-class gate and the Case C
gate.**

The strong induction on `dim_{𝔽_p} E` of `Work.SSGRoute.z_data_general_of_mup_and_aux`, with

* the uniform obligation `AuxExists` replaced by the per-datum `AuxExistsGap` (the statement whose
  no-gap hypothesis is *proved* for the line component by the choice of the line decomposition),
* the uniform no-gap provision `AuxGapProv` replaced by the **Case C gate**: the `z`-data for the
  data whose prescribed local data *and* whose junk ramification both span the coefficient module.

Case C is the exact residual of the argument: it is the only branch of the case analysis in which
neither the peeling step (`csData ≠ ⊤`) nor the spanning step with a line complement of the junk
span (`junkSpan ≠ ⊤`) applies. -/
theorem z_data_general_of_auxGap_and_caseC {K : IntermediateField k Ω}
    [FiniteDimensional k K] [IsGalois k K] [Fintype (K ≃ₐ[k] K)]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (hmup : MupGate (p := p) K)
    (haux : ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), (∀ A ∈ S, SSGRoute.IsFinPlace k A) →
      ZConstruction.AuxExistsGap (p := p) K Λ S)
    (hcc : CaseCGate (p := p) K) :
    ∀ (Λ : IntermediateField k Ω) [FiniteDimensional k Λ] [IsGalois k Λ]
      (S : Finset (ValuationSubring Ω)), ZAmbient (p := p) K Λ S →
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E] (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y →
      ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
  intro Λ _instΛf _instΛg S hAmb
  have key : ∀ (m : ℕ), ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E],
      Module.finrank (ZMod p) E = m → ∀ (y : (Ω ≃ₐ[k] Ω) → E),
      ZHyp (p := p) K Λ S y → ∃ z : (Ω ≃ₐ[k] Ω) → E, HasZData K Λ S y z := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro E _instE _instM _instF hfin y hy
      by_cases hdim : Module.finrank (ZMod p) E ≤ 1
      · exact hmup Λ S hAmb E hdim y hy
      · push_neg at hdim
        by_cases hsp : csData (p := p) K S y = ⊤
        · by_cases hjun : ZConstruction.junkSpan K Λ S y = ⊤
          · exact hcc Λ S hAmb E y hy hsp hjun
          · refine z_data_of_spanning_of_auxGap hAmb hmup (haux Λ S hAmb.hSfin) ?_ y hy hsp hdim hjun
            intro E' _ _ _ hlt y' hy'
            exact ih (Module.finrank (ZMod p) E') (by rw [← hfin]; exact hlt) E' rfl y' hy'
        · haveI : FiniteDimensional (ZMod p) E := Module.Finite.of_finite
          obtain ⟨C, hc⟩ := Submodule.exists_isCompl (csData (p := p) K S y)
          have hlt : Module.finrank (ZMod p) ↥(csData (p := p) K S y) <
              Module.finrank (ZMod p) E := Submodule.finrank_lt hsp
          have hltm : Module.finrank (ZMod p) ↥(csData (p := p) K S y) < m := by
            rw [← hfin]; exact hlt
          have hy' : ZHyp (p := p) K Λ S
              (fun σ => (csData (p := p) K S y).projectionOnto C hc (y σ)) :=
            ZHyp.mapAdd (f := ((csData (p := p) K S y).projectionOnto C hc).toAddMonoidHom) hy
          obtain ⟨z', hz'⟩ := ih _ hltm ↥(csData (p := p) K S y) rfl _ hy'
          have hmap := hasZData_map (A := ↥(csData (p := p) K S y)) (B := E)
            (f := (Submodule.subtype (csData (p := p) K S y)).toAddMonoidHom)
            (fun _ _ h => Subtype.ext h) hz'
          refine ⟨fun σ => (z' σ : E), hasZData_of_fixes_data
            (π := (Submodule.subtype (csData (p := p) K S y)).comp
              ((csData (p := p) K S y).projectionOnto C hc)) ?_ hmap⟩
          intro B hB hconj σ hσK hσd
          have hmem : y σ ∈ csData (p := p) K S y := mem_csData (p := p) (K := K) hB hconj hσK hσd
          show ((Submodule.subtype (csData (p := p) K S y)).comp
            ((csData (p := p) K S y).projectionOnto C hc)) (y σ) = y σ
          rw [LinearMap.comp_apply, Submodule.projectionOnto_apply_of_mem_left _ hmem]
          rfl
  intro E _instE _instM _instF y hy
  exact key (Module.finrank (ZMod p) E) E rfl y hy

/-! ## The level-`N` gap span (the refined criterion of the Case A step) -/

/-- **The level-`N` gap span**: the span of the values of `y` on the inertia groups of the finite
places outside `cs(S)` that are `Λ`-split but not `N`-split.  These are exactly the places at which
`AuxGapFun K Λ S N` must be *checked*, and `AuxGapFun K Λ S N (π ∘ y)` holds as soon as `π` vanishes
on this span.

It is contained in `Work.SSGRoute.ZConstruction.junkSpan K Λ S y` (`gapSpan_le_junkSpan`), and it
shrinks with the level: if `N ≤ N'`, then `gapSpan K Λ S N' y ≤ gapSpan K Λ S N y`
(`gapSpan_mono_level`).  It equals the full junk span as soon as `N` contains the field cut out by
`y` (every place at which `y` ramifies is then not `N`-split), and it is `⊥` for `N = Λ`.  So the
*strictly weaker* hypothesis `gapSpan K Λ S N y ≠ ⊤` suffices for the line decomposition of the Case
A step at the level `N`, in place of `junkSpan K Λ S y ≠ ⊤`. -/
def gapSpan (K Λ : IntermediateField k Ω) (S : Finset (ValuationSubring Ω))
    (N : IntermediateField k Ω) {E : Type} [AddCommGroup E] (y : (Ω ≃ₐ[k] Ω) → E) : AddSubgroup E :=
  AddSubgroup.closure {v : E | ∃ (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω),
    SSGRoute.IsFinPlace k B ∧ (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      SSGRoute.IsSplitIn k Λ B ∧ ¬ SSGRoute.IsSplitIn k N B ∧
      σ ∈ K.fixingSubgroup ∧ SSGRoute.IsInertia k B σ ∧ y σ = v}

/-- The level-`N` gap span is contained in the junk span. -/
theorem gapSpan_le_junkSpan {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [AddCommGroup E]
    (y : (Ω ≃ₐ[k] Ω) → E) :
    gapSpan K Λ S N y ≤ ZConstruction.junkSpan K Λ S y :=
  AddSubgroup.closure_mono (fun _ hv => by
    obtain ⟨B, σ, h1, h2, h3, _h4, h5, h6, h7⟩ := hv
    exact ⟨B, σ, h1, h2, h3, h5, h6, h7⟩)

/-- **The level-`N` gap span grows with the level** (as does `AuxGapFun`, see `AuxGapFun.mono`):
a larger level splits fewer places, so more places are `Λ`-split and not `N`-split.  In particular it
is `⊥` for `N ≤ Λ` (where no place is both `Λ`-split and not `N`-split) and it equals the full junk
span `junkSpan K Λ S y` as soon as `N` contains the field cut out by `y`, so that the criterion
`gapSpan K Λ S N y ≠ ⊤` is *weaker* than `junkSpan K Λ S y ≠ ⊤` for small levels. -/
theorem gapSpan_le_gapSpan_of_le {K Λ N N' : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [AddCommGroup E]
    (y : (Ω ≃ₐ[k] Ω) → E) (hle : N ≤ N') :
    gapSpan K Λ S N y ≤ gapSpan K Λ S N' y :=
  AddSubgroup.closure_mono (fun _ hv => by
    obtain ⟨B, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hv
    exact ⟨B, σ, h1, h2, h3, fun h => h4 (le_trans h (IntermediateField.fixingSubgroup_le hle)),
      h5, h6, h7⟩)

/-- The level-`N` gap span is trivial when the level is contained in `Λ`. -/
theorem gapSpan_eq_bot_of_le_lambda {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E : Type} [AddCommGroup E]
    (y : (Ω ≃ₐ[k] Ω) → E) (hle : N ≤ Λ) :
    gapSpan K Λ S N y = ⊥ := by
  have hset : {v : E | ∃ (B : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω),
      SSGRoute.IsFinPlace k B ∧ (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      SSGRoute.IsSplitIn k Λ B ∧ ¬ SSGRoute.IsSplitIn k N B ∧
      σ ∈ K.fixingSubgroup ∧ SSGRoute.IsInertia k B σ ∧ y σ = v} = ∅ := by
    ext v
    constructor
    · rintro ⟨B, σ, h1, h2, h3, h4, h5, h6, h7⟩
      exact (h4 (fun τ hτ => IntermediateField.fixingSubgroup_le hle (h3 hτ))).elim
    · intro hv
      exact absurd hv (Set.notMem_empty v)
  rw [gapSpan, hset, AddSubgroup.closure_empty]

/-- **The no-gap condition is automatic for a component whose projection kills the level-`N` gap
span.**  This is the level-sharpened form of `auxGapFun_comp_of_junkSpan_le`: the hypothesis
`E₀ ⊇ gapSpan K Λ S N y` is *weaker* than `E₀ ⊇ junkSpan K Λ S y` (it is `gapSpan_le_junkSpan`). -/
theorem auxGapFun_comp_of_gapSpan_le {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (y : (Ω ≃ₐ[k] Ω) → E) (E₀ : AddSubgroup E) (hsub : gapSpan K Λ S N y ≤ E₀)
    (π : E →+ E') (hπ : ∀ x ∈ E₀, π x = 0) :
    ZConstruction.AuxGapFun K Λ S N (fun σ => π (y σ)) :=
  fun B hB hnot hsp hnspt σ hσK hσI =>
    hπ (y σ) (hsub (AddSubgroup.subset_closure
      ⟨B, σ, hB, hnot, hsp, hnspt, hσK, hσI, rfl⟩))

/-- **The gap span of a projection.**  For an additive `π : E → E'` the level-`N` gap span of
`π ∘ y` is contained in `π` of the gap span of `y`. -/
theorem gapSpan_comp_le {K Λ N : IntermediateField k Ω}
    {S : Finset (ValuationSubring Ω)} {E E' : Type} [AddCommGroup E] [AddCommGroup E']
    (π : E →+ E') (y : (Ω ≃ₐ[k] Ω) → E) :
    gapSpan K Λ S N (fun σ => π (y σ)) ≤ (gapSpan K Λ S N y).map π :=
  (AddSubgroup.closure_le _).mpr (fun v hv => by
    obtain ⟨B, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hv
    exact ⟨y σ, AddSubgroup.subset_closure ⟨B, σ, h1, h2, h3, h4, h5, h6, rfl⟩,
      by rw [← h7]⟩)

/-- **The level-`N` gap span *is* the junk span as soon as the level contains the level of the
datum**: if `y` vanishes on `K_y.fixingSubgroup ⊓ K.fixingSubgroup`, then every junk place at which
`y` ramifies is automatically not `N`-split, hence contributes to the gap span.  So the
level-sharpened criterion `gapSpan K Λ S N y ≠ ⊤` is a *strict* weakening of `junkSpan K Λ S y ≠ ⊤`
only for levels `N` not containing the field cut out by `y`; it is a strengthening of nothing. -/
theorem gapSpan_eq_junkSpan_of_level_contains_levelOf {k Ω : Type} [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] {p : ℕ} [Fact p.Prime]
    {K Λ Ky N : IntermediateField k Ω} {S : Finset (ValuationSubring Ω)}
    {E : Type} [AddCommGroup E]
    (y : (Ω ≃ₐ[k] Ω) → E) (hKy : K ≤ Ky) (hN : Ky ≤ N)
    (hvan : ∀ g ∈ Ky.fixingSubgroup, g ∈ K.fixingSubgroup → y g = 0) :
    gapSpan K Λ S N y = ZConstruction.junkSpan K Λ S y := by
  refine le_antisymm (gapSpan_le_junkSpan (K := K) (Λ := Λ) (N := N) y) ?_
  refine (AddSubgroup.closure_le (gapSpan K Λ S N y)).mpr (fun v hv => ?_)
  obtain ⟨B, σ, h1, h2, h3, h4, h5, h6⟩ := hv
  by_cases hsplit : SSGRoute.IsSplitIn k N B
  · have hσN : σ ∈ N.fixingSubgroup := hsplit h5.1
    have hσKy : σ ∈ Ky.fixingSubgroup := IntermediateField.fixingSubgroup_le hN hσN
    have hz : y σ = 0 := hvan σ hσKy h4
    rw [← h6, hz]
    exact AddSubgroup.zero_mem _
  · exact AddSubgroup.subset_closure ⟨B, σ, h1, h2, h3, hsplit, h4, h5, h6⟩

end Work.SSGRoute
