import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles
import Submission.Work.SSGRoute.PTCore.X1_submodule
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.hm_clean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

open IntermediateField

/-! # The formal assembly of `Finite ↥(X¹_S)`

This file proves `finite_X1_S_proved` (Milne, *ADT* I.4.9, `Ш¹`-side) following
`Submission/Work/SSGRoute/Finiteness/STATUS_hm.md` §5.  Nothing here is arithmetic beyond the
already-proved Hermite–Minkowski input `finite_of_bddDegree_unamifiedOutside_proved` and the
already-proved field-of-definition lemma `exists_openSubgroup_factors_of_mem_lcCocycles`.

The two reusable bricks are

* `finite_rightInvariant_functions`: for a finite coefficient module `M` and a finite-index
  subgroup `H ≤ G`, the set of functions `G → M` invariant under right translation by `H` is
  finite (they are the functions on the finite coset space `H\G`);
* `openSubgroup_fixedField_factoring`: an `f : G_k → M` invariant under right translation by an
  open subgroup `U` (which has finite index) is invariant under the *whole* stabiliser of `f`,
  whose fixed field is finite-dimensional over `k` of degree `≤ index U`.  This is what makes the
  `f ↦ L_f` assignment canonical (no choice of representative is needed). -/

/-- **Finite function spaces invariant under a finite-index subgroup.**  If `H ≤ G` has finite
index then a function `f : G → M` with `f (g * u) = f g` for `u ∈ H` is constant on right cosets
of `H`, hence determined by its values on the finite coset space; there are finitely many such
`f` as soon as `M` is finite. -/
theorem finite_rightInvariant_functions {G M : Type} [Group G] [AddCommGroup M] [Finite M]
    (H : Subgroup G) (hH : H.FiniteIndex) :
    {f : G → M | ∀ g u, u ∈ H → f (g * u) = f g}.Finite := by
  classical
  haveI : H.FiniteIndex := hH
  haveI : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Finite (G ⧸ H → M) := inferInstance
  refine Set.finite_coe_iff.mp (Finite.of_injective
    (fun f : ↥{f : G → M | ∀ g u, u ∈ H → f (g * u) = f g} =>
      (fun q : G ⧸ H => Quotient.liftOn q f.1 (fun a b hab => ?_)))
    ?_)
  · -- well-definedness on cosets
    have hab' : a⁻¹ * b ∈ H := QuotientGroup.leftRel_apply.mp hab
    have h := f.2 a (a⁻¹ * b) hab'
    rw [show a * (a⁻¹ * b) = b from by group] at h
    exact h.symm
  · -- injectivity on the quotient function
    intro f g hfg
    apply Subtype.ext
    funext x
    have h := congrFun hfg (QuotientGroup.mk x)
    simpa [Quotient.liftOn_mk] using h

/-- **The canonical field of definition of a function invariant under an open subgroup.**  Let
`U ≤ G_k = Ω ≃ₐ[k] Ω` be open (hence closed, hence of finite index) and let `f : G_k → M` satisfy
`f (g * u) = f g` for `u ∈ U`.  Then `f` is invariant under the whole stabiliser `H` of `f` under
right translation — an open, hence closed, subgroup containing `U` — and the fixed field
`L := Ω^H` of `H` satisfies `U ≤ L.fixingSubgroup = H`, `[L : k] = [G_k : H] ≤ [G_k : U]`, and
`f (g * u) = f g` for every `u ∈ L.fixingSubgroup`. -/
theorem openSubgroup_fixedField_factoring {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsGalois k Ω] {M : Type} (f : (Ω ≃ₐ[k] Ω) → M) (U : Subgroup (Ω ≃ₐ[k] Ω))
    (hUopen : IsOpen (U : Set (Ω ≃ₐ[k] Ω)))
    (hinv : ∀ g u : (Ω ≃ₐ[k] Ω), u ∈ U → f (g * u) = f g) (hUfi : U.FiniteIndex) :
    ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧ U ≤ L.fixingSubgroup ∧
      (∀ g u : (Ω ≃ₐ[k] Ω), u ∈ L.fixingSubgroup → f (g * u) = f g) ∧
      Module.finrank k L ≤ U.index := by
  -- the right stabiliser of `f`
  let H : Subgroup (Ω ≃ₐ[k] Ω) :=
    { carrier := {σ | ∀ g, f (g * σ) = f g}
      one_mem' := by intro g; rw [mul_one]
      mul_mem' := by intro σ ρ hσ hρ g; rw [← mul_assoc, hρ (g * σ), hσ g]
      inv_mem' := by
        intro σ hσ g
        have h := hσ (g * σ⁻¹)
        rw [mul_assoc, inv_mul_cancel, mul_one] at h
        exact h.symm }
  have hUH : U ≤ H := fun u hu g => hinv g u hu
  have hHopen : IsOpen (H : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isOpen_mono hUH hUopen
  have hHclosed : IsClosed (H : Set (Ω ≃ₐ[k] Ω)) := Subgroup.isClosed_of_isOpen H hHopen
  have hHfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hHclosed⟩
  have hHfd : FiniteDimensional k (IntermediateField.fixedField H) := by
    have h2 : IsOpen ((IntermediateField.fixedField H).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) := by
      rw [hHfix]; exact hHopen
    exact (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField H)).mp h2
  have hfin : Module.finrank k (IntermediateField.fixedField H) ≤ U.index := by
    have h1 : Module.finrank k (IntermediateField.fixedField H) =
        (IntermediateField.fixedField H).fixingSubgroup.index :=
      IntermediateField.finrank_eq_fixingSubgroup_index (E' := Ω) _
    rw [h1, hHfix]
    have := hUfi
    exact Subgroup.index_antitone hUH
  refine ⟨IntermediateField.fixedField H, hHfd, ?_, ?_, hfin⟩
  · rw [hHfix]; exact hUH
  · intro g u hu
    rw [hHfix] at hu
    exact hu g

/-- Conjugation of places preserves finiteness (`IsFinPlace` is a `k`-rational notion). -/
theorem isFinPlace_of_isConjPlace {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    {A B : ValuationSubring Ω} (h : SSGRoute.IsConjPlace k A B)
    (hB : SSGRoute.IsFinPlace k B) : SSGRoute.IsFinPlace k A := by
  obtain ⟨σ, hσ⟩ := h
  have hA : A = σ⁻¹ • B := by rw [← hσ, inv_smul_smul]
  rw [hA]
  exact (Work.SSGRoute.isFinPlace_smul_iff B σ⁻¹).mpr hB

/-- **Finiteness of `X¹_S`** (Milne, *Arithmetic Duality Theorems*, Lemma I.4.9, `Ш¹`-side, at a finite level `K/k` and a finite coefficient module `M`).  Verbatim the statement of `Work.SSGRoute.PTCore.finite_X1_S` (a `sorry` stub of the `PTCore` lane, and one of the two finiteness inputs of Route B of `Work.SSGRoute.PTCore.pt_pairing_left_inj`).

No arithmetic beyond Hermite–Minkowski is needed; the route is worked out in
`Submission/Work/SSGRoute/Finiteness/STATUS_hm.md` §4–§5:

* `X1 S = Submodule.map (Submodule.mkQ …) (comap subtype (Z1unr … S) ⊓ comap subtype (Z1locOn … ↑S))`, so `Finite` is preserved by the image: it suffices that the *cochain* set `{f // f ∈ Z1unr S ∧ f ∈ Z1locOn ↑S}` is finite;
* for `f ∈ Z1unr S`, `Work.SSGRoute.Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles` (green) produces an open `U_f ≤ G_k` with `Subgroup.index U_f ≤ Nat.card M`, containing every inertia group `I_B` for `B` outside the conjugacy classes of `S`, and with `∀ g u ∈ U_f, f (g*u) = f g` — i.e. `f` factors through `G_k/U_f`; its fixed field `L_f := Ω^{U_f}` has `[L_f : k] = index U_f ≤ Nat.card M` (open subgroups are closed) and is k-ramified only inside `S`;
* by `Work.SSGRoute.TatePoitouRoute.FinitenessHM.finite_of_bddDegree_unamifiedOutside_proved` (`(HM)`) there are only finitely many such `L_f`; note `(HM)` carries `hS : ∀ A ∈ S, IsFinPlace k A` while the target does not, so apply it to `S.filter (IsFinPlace k)` (`Z1unr` constrains only *finite* places `B`, and `IsConjPlace k A B` for finite `B` forces `IsFinPlace k A`, so the cochain set is unchanged); for each fixed `L` the cochains factoring through `G_k/U` are in bijection with `G_k/U → M`, which is finite; so `Z1unr S` is a finite union of finite sets, and a subset of a finite set is finite.  No canonical representative of a class is needed (this is the key point of §5).  (`G_k/U_f` is only a quotient for non-normal `U_f`; the count is unaffected — no group structure on the index set is needed.) -/
theorem finite_X1_S_proved
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [Fintype (K ≃ₐ[k] K)]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) :
    Finite ↥(Work.SSGRoute.PTCore.X1 p k Ω K M S) := by
  classical
  -- The finite place set actually constrained by `Z1unr`, and the bound on the degree.
  let T : Finset (ValuationSubring Ω) := S.filter (fun A => SSGRoute.IsFinPlace k A)
  let n : ℕ := Nat.card M
  -- The Hermite–Minkowski list of fields of degree `≤ n` ramified only inside `T`.
  let 𝓛 : Set {F : IntermediateField k Ω // FiniteDimensional k F} :=
    {L | Module.finrank k L.1 ≤ n ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B → SSGRoute.IsRamifiedIn k L.1 B →
        ∃ A ∈ T, SSGRoute.IsConjPlace k A B)}
  have hHM : 𝓛.Finite :=
    finite_of_bddDegree_unamifiedOutside_clean k Ω T
      (fun A hA => (Finset.mem_filter.mp hA).2) n
  -- The finite set of cochains attached to a field `L`: those invariant under `Gal(Ω/L)`.
  let B : {F : IntermediateField k Ω // FiniteDimensional k F} → Set ((Ω ≃ₐ[k] Ω) → M) :=
    fun L => {f | ∀ g u : (Ω ≃ₐ[k] Ω), u ∈ L.1.fixingSubgroup → f (g * u) = f g}
  have hBfin : ∀ L : {F : IntermediateField k Ω // FiniteDimensional k F}, (B L).Finite := by
    intro L
    haveI : FiniteDimensional k L.1 := L.2
    have hq : Finite ((Ω ≃ₐ[k] Ω) ⧸ L.1.fixingSubgroup) :=
      Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen L.1)
    exact finite_rightInvariant_functions L.1.fixingSubgroup
      (Subgroup.finiteIndex_iff_finite_quotient.mpr hq)
  -- Every unramified-outside-`S` cocycle factors through a field of the finite list `𝓛`.
  have hZsub : {f : (Ω ≃ₐ[k] Ω) → M | f ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K M S} ⊆
      ⋃ L ∈ 𝓛, B L := by
    intro f hf
    obtain ⟨hcoc, hlc, hunr⟩ := hf
    have hflc : f ∈ Work.SSGRoute.lcCocycles p k Ω K M ⊤ :=
      (Work.SSGRoute.mem_lcCocycles p k Ω K M ⊤ f).mpr ⟨hcoc, hlc⟩
    obtain ⟨U, hUfi, hUopen, hinv, hUinertia, hUindex⟩ :=
      Work.SSGRoute.Finiteness.exists_openSubgroup_factors_of_mem_lcCocycles
        p k Ω K M S f hflc hunr
    obtain ⟨L, hLfd, hUL, hLinv, hLfin⟩ :=
      openSubgroup_fixedField_factoring f U hUopen hinv hUfi
    have hLram : ∀ B' : ValuationSubring Ω, SSGRoute.IsFinPlace k B' →
        SSGRoute.IsRamifiedIn k L B' → ∃ A ∈ T, SSGRoute.IsConjPlace k A B' := by
      intro B' hB' hram
      by_contra hno
      obtain ⟨σ, hσin, hσnotin⟩ := hram
      have hconj : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B' := by
        intro A hAS hAC
        exact hno ⟨A, Finset.mem_filter.mpr
          ⟨hAS, isFinPlace_of_isConjPlace hAC hB'⟩, hAC⟩
      have hIB : Work.SSGRoute.inertiaSub k Ω B' ≤ U := hUinertia B' hB' hconj
      have hσU : σ ∈ U := hIB ((Work.SSGRoute.mem_inertiaSub k Ω B' σ).mpr hσin)
      exact hσnotin (hUL hσU)
    have hLmem : (⟨L, hLfd⟩ : {F : IntermediateField k Ω // FiniteDimensional k F}) ∈ 𝓛 :=
      ⟨le_trans hLfin hUindex, hLram⟩
    refine Set.mem_iUnion.mpr ⟨⟨L, hLfd⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hLmem, ?_⟩
    intro g u hu
    exact hLinv g u hu
  have hunion : (⋃ L ∈ 𝓛, B L).Finite := hHM.biUnion (fun L _ => hBfin L)
  have hZfin : {f : (Ω ≃ₐ[k] Ω) → M |
      f ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K M S}.Finite := hunion.subset hZsub
  -- Intersect with the local-triviality condition: a subset of a finite set is finite.
  let Zc : Set ((Ω ≃ₐ[k] Ω) → M) :=
    {f | f ∈ Work.SSGRoute.PTCore.Z1unr p k Ω K M S ∧
      f ∈ Work.SSGRoute.PTCore.Z1locOn p k Ω K M (↑S : Set (ValuationSubring Ω))}
  have hZcfin : Zc.Finite := hZfin.subset (fun f hf => hf.1)
  haveI : Finite ↥Zc := Set.finite_coe_iff.mpr hZcfin
  -- The cochain-level set of `X1 S`, as a submodule of `↥(lcCocycles ⊤)`.
  let W : Submodule (ZMod p) (↥(Work.SSGRoute.lcCocycles p k Ω K M ⊤)) :=
    Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M ⊤).subtype
        (Work.SSGRoute.PTCore.Z1unr p k Ω K M S) ⊓
      Submodule.comap (Work.SSGRoute.lcCocycles p k Ω K M ⊤).subtype
        (Work.SSGRoute.PTCore.Z1locOn p k Ω K M (↑S : Set (ValuationSubring Ω)))
  have hWfin : Finite ↥W := by
    refine Finite.of_injective
      (fun a : ↥W => (⟨(a.1 : (Ω ≃ₐ[k] Ω) → M), ?_, ?_⟩ : ↥Zc)) ?_
    · exact Submodule.mem_comap.mp (Submodule.mem_inf.mp a.2).1
    · exact Submodule.mem_comap.mp (Submodule.mem_inf.mp a.2).2
    · intro a b hab
      have h1 : (a.1 : (Ω ≃ₐ[k] Ω) → M) = (b.1 : (Ω ≃ₐ[k] Ω) → M) :=
        congrArg (fun z : ↥Zc => z.1) hab
      exact Subtype.ext (Subtype.ext h1)
  -- `X1 S` is the image of `W`, and `Finite` is preserved by surjections.
  haveI : Finite ↥W := hWfin
  refine Finite.of_surjective
    (fun a : ↥W => (⟨Submodule.mkQ _ a.1, Submodule.mem_map_of_mem a.2⟩ :
      ↥(Work.SSGRoute.PTCore.X1 p k Ω K M S))) ?_
  rintro ⟨y, hy⟩
  have hy' : y ∈ Submodule.map (Submodule.mkQ ((Work.SSGRoute.B1top p k Ω K M).comap
      (Work.SSGRoute.lcCocycles p k Ω K M ⊤).subtype)) W := hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy'
  exact ⟨⟨a, ha⟩, rfl⟩

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
